%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:01 EST 2020

% Result     : Theorem 10.48s
% Output     : CNFRefutation 10.54s
% Verified   : 
% Statistics : Number of formulae       :  233 (9652 expanded)
%              Number of leaves         :   48 (3193 expanded)
%              Depth                    :   22
%              Number of atoms          :  481 (23720 expanded)
%              Number of equality atoms :  106 (5856 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_174,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_139,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_119,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_161,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_159,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_135,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => ( v1_funct_1(k2_funct_2(A,B))
        & v1_funct_2(k2_funct_2(A,B),A,A)
        & v3_funct_2(k2_funct_2(A,B),A,A)
        & m1_subset_1(k2_funct_2(A,B),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).

tff(f_149,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_111,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_78,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_13745,plain,(
    ! [C_1059,A_1060,B_1061] :
      ( v1_relat_1(C_1059)
      | ~ m1_subset_1(C_1059,k1_zfmisc_1(k2_zfmisc_1(A_1060,B_1061))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_13758,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_13745])).

tff(c_84,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_80,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_15120,plain,(
    ! [C_1208,A_1209,B_1210] :
      ( v2_funct_1(C_1208)
      | ~ v3_funct_2(C_1208,A_1209,B_1210)
      | ~ v1_funct_1(C_1208)
      | ~ m1_subset_1(C_1208,k1_zfmisc_1(k2_zfmisc_1(A_1209,B_1210))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_15133,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_15120])).

tff(c_15138,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_15133])).

tff(c_68,plain,(
    ! [A_33] : m1_subset_1(k6_partfun1(A_33),k1_zfmisc_1(k2_zfmisc_1(A_33,A_33))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_15329,plain,(
    ! [A_1237,B_1238,C_1239,D_1240] :
      ( r2_relset_1(A_1237,B_1238,C_1239,C_1239)
      | ~ m1_subset_1(D_1240,k1_zfmisc_1(k2_zfmisc_1(A_1237,B_1238)))
      | ~ m1_subset_1(C_1239,k1_zfmisc_1(k2_zfmisc_1(A_1237,B_1238))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_15567,plain,(
    ! [A_1265,C_1266] :
      ( r2_relset_1(A_1265,A_1265,C_1266,C_1266)
      | ~ m1_subset_1(C_1266,k1_zfmisc_1(k2_zfmisc_1(A_1265,A_1265))) ) ),
    inference(resolution,[status(thm)],[c_68,c_15329])).

tff(c_15579,plain,(
    ! [A_33] : r2_relset_1(A_33,A_33,k6_partfun1(A_33),k6_partfun1(A_33)) ),
    inference(resolution,[status(thm)],[c_68,c_15567])).

tff(c_13828,plain,(
    ! [C_1069,B_1070,A_1071] :
      ( v5_relat_1(C_1069,B_1070)
      | ~ m1_subset_1(C_1069,k1_zfmisc_1(k2_zfmisc_1(A_1071,B_1070))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_13841,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_78,c_13828])).

tff(c_14074,plain,(
    ! [B_1097,A_1098] :
      ( k2_relat_1(B_1097) = A_1098
      | ~ v2_funct_2(B_1097,A_1098)
      | ~ v5_relat_1(B_1097,A_1098)
      | ~ v1_relat_1(B_1097) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_14089,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_13841,c_14074])).

tff(c_14104,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13758,c_14089])).

tff(c_14131,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_14104])).

tff(c_14614,plain,(
    ! [C_1159,B_1160,A_1161] :
      ( v2_funct_2(C_1159,B_1160)
      | ~ v3_funct_2(C_1159,A_1161,B_1160)
      | ~ v1_funct_1(C_1159)
      | ~ m1_subset_1(C_1159,k1_zfmisc_1(k2_zfmisc_1(A_1161,B_1160))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_14627,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_14614])).

tff(c_14632,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_14627])).

tff(c_14634,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14131,c_14632])).

tff(c_14635,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_14104])).

tff(c_74,plain,(
    ! [A_42] : k6_relat_1(A_42) = k6_partfun1(A_42) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_22,plain,(
    ! [A_9] :
      ( k5_relat_1(k2_funct_1(A_9),A_9) = k6_relat_1(k2_relat_1(A_9))
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_86,plain,(
    ! [A_9] :
      ( k5_relat_1(k2_funct_1(A_9),A_9) = k6_partfun1(k2_relat_1(A_9))
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_22])).

tff(c_82,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_15711,plain,(
    ! [A_1279,B_1280] :
      ( k2_funct_2(A_1279,B_1280) = k2_funct_1(B_1280)
      | ~ m1_subset_1(B_1280,k1_zfmisc_1(k2_zfmisc_1(A_1279,A_1279)))
      | ~ v3_funct_2(B_1280,A_1279,A_1279)
      | ~ v1_funct_2(B_1280,A_1279,A_1279)
      | ~ v1_funct_1(B_1280) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_15725,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_15711])).

tff(c_15730,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_15725])).

tff(c_15651,plain,(
    ! [A_1274,B_1275] :
      ( v1_funct_1(k2_funct_2(A_1274,B_1275))
      | ~ m1_subset_1(B_1275,k1_zfmisc_1(k2_zfmisc_1(A_1274,A_1274)))
      | ~ v3_funct_2(B_1275,A_1274,A_1274)
      | ~ v1_funct_2(B_1275,A_1274,A_1274)
      | ~ v1_funct_1(B_1275) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_15665,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_15651])).

tff(c_15670,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_15665])).

tff(c_15731,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15730,c_15670])).

tff(c_58,plain,(
    ! [A_31,B_32] :
      ( m1_subset_1(k2_funct_2(A_31,B_32),k1_zfmisc_1(k2_zfmisc_1(A_31,A_31)))
      | ~ m1_subset_1(B_32,k1_zfmisc_1(k2_zfmisc_1(A_31,A_31)))
      | ~ v3_funct_2(B_32,A_31,A_31)
      | ~ v1_funct_2(B_32,A_31,A_31)
      | ~ v1_funct_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_16456,plain,(
    ! [B_1333,A_1329,F_1331,D_1330,C_1334,E_1332] :
      ( k1_partfun1(A_1329,B_1333,C_1334,D_1330,E_1332,F_1331) = k5_relat_1(E_1332,F_1331)
      | ~ m1_subset_1(F_1331,k1_zfmisc_1(k2_zfmisc_1(C_1334,D_1330)))
      | ~ v1_funct_1(F_1331)
      | ~ m1_subset_1(E_1332,k1_zfmisc_1(k2_zfmisc_1(A_1329,B_1333)))
      | ~ v1_funct_1(E_1332) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_16469,plain,(
    ! [A_1329,B_1333,E_1332] :
      ( k1_partfun1(A_1329,B_1333,'#skF_1','#skF_1',E_1332,'#skF_2') = k5_relat_1(E_1332,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_1332,k1_zfmisc_1(k2_zfmisc_1(A_1329,B_1333)))
      | ~ v1_funct_1(E_1332) ) ),
    inference(resolution,[status(thm)],[c_78,c_16456])).

tff(c_16483,plain,(
    ! [A_1335,B_1336,E_1337] :
      ( k1_partfun1(A_1335,B_1336,'#skF_1','#skF_1',E_1337,'#skF_2') = k5_relat_1(E_1337,'#skF_2')
      | ~ m1_subset_1(E_1337,k1_zfmisc_1(k2_zfmisc_1(A_1335,B_1336)))
      | ~ v1_funct_1(E_1337) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_16469])).

tff(c_17145,plain,(
    ! [A_1365,B_1366] :
      ( k1_partfun1(A_1365,A_1365,'#skF_1','#skF_1',k2_funct_2(A_1365,B_1366),'#skF_2') = k5_relat_1(k2_funct_2(A_1365,B_1366),'#skF_2')
      | ~ v1_funct_1(k2_funct_2(A_1365,B_1366))
      | ~ m1_subset_1(B_1366,k1_zfmisc_1(k2_zfmisc_1(A_1365,A_1365)))
      | ~ v3_funct_2(B_1366,A_1365,A_1365)
      | ~ v1_funct_2(B_1366,A_1365,A_1365)
      | ~ v1_funct_1(B_1366) ) ),
    inference(resolution,[status(thm)],[c_58,c_16483])).

tff(c_17161,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2') = k5_relat_1(k2_funct_2('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_17145])).

tff(c_17173,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2') = k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_15731,c_15730,c_15730,c_15730,c_17161])).

tff(c_7611,plain,(
    ! [C_628,B_629,A_630] :
      ( v2_funct_2(C_628,B_629)
      | ~ v3_funct_2(C_628,A_630,B_629)
      | ~ v1_funct_1(C_628)
      | ~ m1_subset_1(C_628,k1_zfmisc_1(k2_zfmisc_1(A_630,B_629))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_7624,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_7611])).

tff(c_7629,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_7624])).

tff(c_148,plain,(
    ! [C_58,A_59,B_60] :
      ( v1_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_161,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_148])).

tff(c_1257,plain,(
    ! [C_172,A_173,B_174] :
      ( v2_funct_1(C_172)
      | ~ v3_funct_2(C_172,A_173,B_174)
      | ~ v1_funct_1(C_172)
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(A_173,B_174))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1270,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_1257])).

tff(c_1275,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_1270])).

tff(c_1705,plain,(
    ! [A_232,B_233,C_234,D_235] :
      ( r2_relset_1(A_232,B_233,C_234,C_234)
      | ~ m1_subset_1(D_235,k1_zfmisc_1(k2_zfmisc_1(A_232,B_233)))
      | ~ m1_subset_1(C_234,k1_zfmisc_1(k2_zfmisc_1(A_232,B_233))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1719,plain,(
    ! [A_236,C_237] :
      ( r2_relset_1(A_236,A_236,C_237,C_237)
      | ~ m1_subset_1(C_237,k1_zfmisc_1(k2_zfmisc_1(A_236,A_236))) ) ),
    inference(resolution,[status(thm)],[c_68,c_1705])).

tff(c_1731,plain,(
    ! [A_33] : r2_relset_1(A_33,A_33,k6_partfun1(A_33),k6_partfun1(A_33)) ),
    inference(resolution,[status(thm)],[c_68,c_1719])).

tff(c_259,plain,(
    ! [C_76,B_77,A_78] :
      ( v5_relat_1(C_76,B_77)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_78,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_272,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_78,c_259])).

tff(c_477,plain,(
    ! [B_99,A_100] :
      ( k2_relat_1(B_99) = A_100
      | ~ v2_funct_2(B_99,A_100)
      | ~ v5_relat_1(B_99,A_100)
      | ~ v1_relat_1(B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_492,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_272,c_477])).

tff(c_507,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_492])).

tff(c_535,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_507])).

tff(c_919,plain,(
    ! [C_145,B_146,A_147] :
      ( v2_funct_2(C_145,B_146)
      | ~ v3_funct_2(C_145,A_147,B_146)
      | ~ v1_funct_1(C_145)
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(A_147,B_146))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_932,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_919])).

tff(c_937,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_932])).

tff(c_939,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_535,c_937])).

tff(c_940,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_507])).

tff(c_18,plain,(
    ! [A_8] :
      ( k2_relat_1(A_8) != k1_xboole_0
      | k1_xboole_0 = A_8
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_168,plain,
    ( k2_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_161,c_18])).

tff(c_179,plain,(
    k2_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_168])).

tff(c_942,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_940,c_179])).

tff(c_1090,plain,(
    ! [A_159,B_160,C_161] :
      ( k1_relset_1(A_159,B_160,C_161) = k1_relat_1(C_161)
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(A_159,B_160))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1107,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_1090])).

tff(c_1663,plain,(
    ! [B_228,A_229,C_230] :
      ( k1_xboole_0 = B_228
      | k1_relset_1(A_229,B_228,C_230) = A_229
      | ~ v1_funct_2(C_230,A_229,B_228)
      | ~ m1_subset_1(C_230,k1_zfmisc_1(k2_zfmisc_1(A_229,B_228))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1676,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_78,c_1663])).

tff(c_1683,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1107,c_1676])).

tff(c_1684,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_942,c_1683])).

tff(c_24,plain,(
    ! [A_9] :
      ( k5_relat_1(A_9,k2_funct_1(A_9)) = k6_relat_1(k1_relat_1(A_9))
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_85,plain,(
    ! [A_9] :
      ( k5_relat_1(A_9,k2_funct_1(A_9)) = k6_partfun1(k1_relat_1(A_9))
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_24])).

tff(c_1875,plain,(
    ! [A_252,B_253] :
      ( k2_funct_2(A_252,B_253) = k2_funct_1(B_253)
      | ~ m1_subset_1(B_253,k1_zfmisc_1(k2_zfmisc_1(A_252,A_252)))
      | ~ v3_funct_2(B_253,A_252,A_252)
      | ~ v1_funct_2(B_253,A_252,A_252)
      | ~ v1_funct_1(B_253) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_1889,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_1875])).

tff(c_1894,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_1889])).

tff(c_1743,plain,(
    ! [A_239,B_240] :
      ( v1_funct_1(k2_funct_2(A_239,B_240))
      | ~ m1_subset_1(B_240,k1_zfmisc_1(k2_zfmisc_1(A_239,A_239)))
      | ~ v3_funct_2(B_240,A_239,A_239)
      | ~ v1_funct_2(B_240,A_239,A_239)
      | ~ v1_funct_1(B_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1757,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_1743])).

tff(c_1762,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_1757])).

tff(c_1895,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1894,c_1762])).

tff(c_2159,plain,(
    ! [A_287,B_288] :
      ( m1_subset_1(k2_funct_2(A_287,B_288),k1_zfmisc_1(k2_zfmisc_1(A_287,A_287)))
      | ~ m1_subset_1(B_288,k1_zfmisc_1(k2_zfmisc_1(A_287,A_287)))
      | ~ v3_funct_2(B_288,A_287,A_287)
      | ~ v1_funct_2(B_288,A_287,A_287)
      | ~ v1_funct_1(B_288) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_2211,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1894,c_2159])).

tff(c_2236,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_2211])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2310,plain,(
    r1_tarski(k2_funct_1('#skF_2'),k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_2236,c_10])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2354,plain,(
    ! [B_293,A_289,E_292,D_290,C_294,F_291] :
      ( k1_partfun1(A_289,B_293,C_294,D_290,E_292,F_291) = k5_relat_1(E_292,F_291)
      | ~ m1_subset_1(F_291,k1_zfmisc_1(k2_zfmisc_1(C_294,D_290)))
      | ~ v1_funct_1(F_291)
      | ~ m1_subset_1(E_292,k1_zfmisc_1(k2_zfmisc_1(A_289,B_293)))
      | ~ v1_funct_1(E_292) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_5606,plain,(
    ! [B_453,C_450,A_455,D_454,A_452,E_451] :
      ( k1_partfun1(A_452,B_453,C_450,D_454,E_451,A_455) = k5_relat_1(E_451,A_455)
      | ~ v1_funct_1(A_455)
      | ~ m1_subset_1(E_451,k1_zfmisc_1(k2_zfmisc_1(A_452,B_453)))
      | ~ v1_funct_1(E_451)
      | ~ r1_tarski(A_455,k2_zfmisc_1(C_450,D_454)) ) ),
    inference(resolution,[status(thm)],[c_12,c_2354])).

tff(c_5625,plain,(
    ! [C_450,D_454,A_455] :
      ( k1_partfun1('#skF_1','#skF_1',C_450,D_454,'#skF_2',A_455) = k5_relat_1('#skF_2',A_455)
      | ~ v1_funct_1(A_455)
      | ~ v1_funct_1('#skF_2')
      | ~ r1_tarski(A_455,k2_zfmisc_1(C_450,D_454)) ) ),
    inference(resolution,[status(thm)],[c_78,c_5606])).

tff(c_5650,plain,(
    ! [C_456,D_457,A_458] :
      ( k1_partfun1('#skF_1','#skF_1',C_456,D_457,'#skF_2',A_458) = k5_relat_1('#skF_2',A_458)
      | ~ v1_funct_1(A_458)
      | ~ r1_tarski(A_458,k2_zfmisc_1(C_456,D_457)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_5625])).

tff(c_5665,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2310,c_5650])).

tff(c_5699,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1895,c_5665])).

tff(c_76,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1'))
    | ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_101,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_1896,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1894,c_101])).

tff(c_6036,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5699,c_1896])).

tff(c_6043,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k1_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_6036])).

tff(c_6046,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_84,c_1275,c_1731,c_1684,c_6043])).

tff(c_6047,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_168])).

tff(c_6048,plain,(
    k2_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_168])).

tff(c_6071,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6047,c_6048])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6052,plain,(
    ! [A_3] : r1_tarski('#skF_2',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6047,c_8])).

tff(c_6113,plain,(
    ! [B_475,A_476] :
      ( v5_relat_1(B_475,A_476)
      | ~ r1_tarski(k2_relat_1(B_475),A_476)
      | ~ v1_relat_1(B_475) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6116,plain,(
    ! [A_476] :
      ( v5_relat_1('#skF_2',A_476)
      | ~ r1_tarski('#skF_2',A_476)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6071,c_6113])).

tff(c_6122,plain,(
    ! [A_476] : v5_relat_1('#skF_2',A_476) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_6052,c_6116])).

tff(c_6351,plain,(
    ! [B_504,A_505] :
      ( k2_relat_1(B_504) = A_505
      | ~ v2_funct_2(B_504,A_505)
      | ~ v5_relat_1(B_504,A_505)
      | ~ v1_relat_1(B_504) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_6363,plain,(
    ! [A_476] :
      ( k2_relat_1('#skF_2') = A_476
      | ~ v2_funct_2('#skF_2',A_476)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_6122,c_6351])).

tff(c_6374,plain,(
    ! [A_476] :
      ( A_476 = '#skF_2'
      | ~ v2_funct_2('#skF_2',A_476) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_6071,c_6363])).

tff(c_7633,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_7629,c_6374])).

tff(c_7671,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7633,c_6052])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_7899,plain,(
    ! [A_641,B_642,C_643,D_644] :
      ( r2_relset_1(A_641,B_642,C_643,C_643)
      | ~ m1_subset_1(D_644,k1_zfmisc_1(k2_zfmisc_1(A_641,B_642)))
      | ~ m1_subset_1(C_643,k1_zfmisc_1(k2_zfmisc_1(A_641,B_642))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_8946,plain,(
    ! [A_768,B_769,C_770,A_771] :
      ( r2_relset_1(A_768,B_769,C_770,C_770)
      | ~ m1_subset_1(C_770,k1_zfmisc_1(k2_zfmisc_1(A_768,B_769)))
      | ~ r1_tarski(A_771,k2_zfmisc_1(A_768,B_769)) ) ),
    inference(resolution,[status(thm)],[c_12,c_7899])).

tff(c_10238,plain,(
    ! [A_874,B_875,A_876,A_877] :
      ( r2_relset_1(A_874,B_875,A_876,A_876)
      | ~ r1_tarski(A_877,k2_zfmisc_1(A_874,B_875))
      | ~ r1_tarski(A_876,k2_zfmisc_1(A_874,B_875)) ) ),
    inference(resolution,[status(thm)],[c_12,c_8946])).

tff(c_10255,plain,(
    ! [A_878,B_879,A_880] :
      ( r2_relset_1(A_878,B_879,A_880,A_880)
      | ~ r1_tarski(A_880,k2_zfmisc_1(A_878,B_879)) ) ),
    inference(resolution,[status(thm)],[c_6,c_10238])).

tff(c_10269,plain,(
    ! [A_878,B_879] : r2_relset_1(A_878,B_879,'#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_7671,c_10255])).

tff(c_7678,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7633,c_84])).

tff(c_7674,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7633,c_161])).

tff(c_6712,plain,(
    ! [C_537,A_538,B_539] :
      ( v2_funct_1(C_537)
      | ~ v3_funct_2(C_537,A_538,B_539)
      | ~ v1_funct_1(C_537)
      | ~ m1_subset_1(C_537,k1_zfmisc_1(k2_zfmisc_1(A_538,B_539))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_6725,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_6712])).

tff(c_6730,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_6725])).

tff(c_7645,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7633,c_6730])).

tff(c_160,plain,(
    ! [A_33] : v1_relat_1(k6_partfun1(A_33)) ),
    inference(resolution,[status(thm)],[c_68,c_148])).

tff(c_6182,plain,(
    ! [C_488,B_489,A_490] :
      ( v5_relat_1(C_488,B_489)
      | ~ m1_subset_1(C_488,k1_zfmisc_1(k2_zfmisc_1(A_490,B_489))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_6194,plain,(
    ! [A_33] : v5_relat_1(k6_partfun1(A_33),A_33) ),
    inference(resolution,[status(thm)],[c_68,c_6182])).

tff(c_6201,plain,(
    ! [B_495,A_496] :
      ( r1_tarski(k2_relat_1(B_495),A_496)
      | ~ v5_relat_1(B_495,A_496)
      | ~ v1_relat_1(B_495) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_118,plain,(
    ! [B_54,A_55] :
      ( B_54 = A_55
      | ~ r1_tarski(B_54,A_55)
      | ~ r1_tarski(A_55,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_130,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_118])).

tff(c_6049,plain,(
    ! [A_3] :
      ( A_3 = '#skF_2'
      | ~ r1_tarski(A_3,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6047,c_6047,c_130])).

tff(c_6252,plain,(
    ! [B_502] :
      ( k2_relat_1(B_502) = '#skF_2'
      | ~ v5_relat_1(B_502,'#skF_2')
      | ~ v1_relat_1(B_502) ) ),
    inference(resolution,[status(thm)],[c_6201,c_6049])).

tff(c_6260,plain,
    ( k2_relat_1(k6_partfun1('#skF_2')) = '#skF_2'
    | ~ v1_relat_1(k6_partfun1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_6194,c_6252])).

tff(c_6270,plain,(
    k2_relat_1(k6_partfun1('#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_6260])).

tff(c_170,plain,(
    ! [A_61] : v1_relat_1(k6_partfun1(A_61)) ),
    inference(resolution,[status(thm)],[c_68,c_148])).

tff(c_177,plain,(
    ! [A_61] :
      ( k2_relat_1(k6_partfun1(A_61)) != k1_xboole_0
      | k6_partfun1(A_61) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_170,c_18])).

tff(c_6132,plain,(
    ! [A_61] :
      ( k2_relat_1(k6_partfun1(A_61)) != '#skF_2'
      | k6_partfun1(A_61) = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6047,c_6047,c_177])).

tff(c_6291,plain,(
    k6_partfun1('#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_6270,c_6132])).

tff(c_7661,plain,(
    k6_partfun1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7633,c_7633,c_6291])).

tff(c_7672,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7633,c_7633,c_6071])).

tff(c_7677,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7633,c_82])).

tff(c_7676,plain,(
    v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7633,c_80])).

tff(c_6096,plain,(
    ! [A_472,A_473,B_474] :
      ( v1_relat_1(A_472)
      | ~ r1_tarski(A_472,k2_zfmisc_1(A_473,B_474)) ) ),
    inference(resolution,[status(thm)],[c_12,c_148])).

tff(c_6112,plain,(
    ! [A_473,B_474] : v1_relat_1(k2_zfmisc_1(A_473,B_474)) ),
    inference(resolution,[status(thm)],[c_6,c_6096])).

tff(c_6229,plain,(
    ! [A_497,B_498,A_499] :
      ( v5_relat_1(A_497,B_498)
      | ~ r1_tarski(A_497,k2_zfmisc_1(A_499,B_498)) ) ),
    inference(resolution,[status(thm)],[c_12,c_6182])).

tff(c_6250,plain,(
    ! [A_499,B_498] : v5_relat_1(k2_zfmisc_1(A_499,B_498),B_498) ),
    inference(resolution,[status(thm)],[c_6,c_6229])).

tff(c_6256,plain,(
    ! [A_499] :
      ( k2_relat_1(k2_zfmisc_1(A_499,'#skF_2')) = '#skF_2'
      | ~ v1_relat_1(k2_zfmisc_1(A_499,'#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_6250,c_6252])).

tff(c_6267,plain,(
    ! [A_499] : k2_relat_1(k2_zfmisc_1(A_499,'#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6112,c_6256])).

tff(c_6150,plain,(
    ! [A_484] :
      ( k2_relat_1(A_484) != '#skF_2'
      | A_484 = '#skF_2'
      | ~ v1_relat_1(A_484) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6047,c_6047,c_18])).

tff(c_6545,plain,(
    ! [A_522,B_523] :
      ( k2_relat_1(k2_zfmisc_1(A_522,B_523)) != '#skF_2'
      | k2_zfmisc_1(A_522,B_523) = '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_6112,c_6150])).

tff(c_6549,plain,(
    ! [A_499] : k2_zfmisc_1(A_499,'#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_6267,c_6545])).

tff(c_6319,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_6291,c_68])).

tff(c_6551,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6549,c_6319])).

tff(c_7654,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7633,c_7633,c_6551])).

tff(c_7655,plain,(
    ! [A_499] : k2_zfmisc_1(A_499,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7633,c_7633,c_6549])).

tff(c_8000,plain,(
    ! [A_655,B_656] :
      ( k2_funct_2(A_655,B_656) = k2_funct_1(B_656)
      | ~ m1_subset_1(B_656,k1_zfmisc_1(k2_zfmisc_1(A_655,A_655)))
      | ~ v3_funct_2(B_656,A_655,A_655)
      | ~ v1_funct_2(B_656,A_655,A_655)
      | ~ v1_funct_1(B_656) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_9282,plain,(
    ! [A_813] :
      ( k2_funct_2(A_813,k6_partfun1(A_813)) = k2_funct_1(k6_partfun1(A_813))
      | ~ v3_funct_2(k6_partfun1(A_813),A_813,A_813)
      | ~ v1_funct_2(k6_partfun1(A_813),A_813,A_813)
      | ~ v1_funct_1(k6_partfun1(A_813)) ) ),
    inference(resolution,[status(thm)],[c_68,c_8000])).

tff(c_9285,plain,
    ( k2_funct_2('#skF_1',k6_partfun1('#skF_1')) = k2_funct_1(k6_partfun1('#skF_1'))
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2(k6_partfun1('#skF_1'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k6_partfun1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7661,c_9282])).

tff(c_9287,plain,(
    k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7678,c_7661,c_7677,c_7661,c_7676,c_7661,c_7661,c_9285])).

tff(c_9293,plain,
    ( m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_9287,c_58])).

tff(c_9297,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7678,c_7677,c_7676,c_7654,c_7655,c_7655,c_9293])).

tff(c_9327,plain,(
    r1_tarski(k2_funct_1('#skF_1'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_9297,c_10])).

tff(c_7669,plain,(
    ! [A_3] :
      ( A_3 = '#skF_1'
      | ~ r1_tarski(A_3,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7633,c_7633,c_6049])).

tff(c_9355,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_9327,c_7669])).

tff(c_9372,plain,
    ( k6_partfun1(k2_relat_1('#skF_1')) = k5_relat_1('#skF_1','#skF_1')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_9355,c_86])).

tff(c_9379,plain,(
    k5_relat_1('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7674,c_7678,c_7645,c_7661,c_7672,c_9372])).

tff(c_8195,plain,(
    ! [C_677,F_674,A_672,B_676,D_673,E_675] :
      ( k1_partfun1(A_672,B_676,C_677,D_673,E_675,F_674) = k5_relat_1(E_675,F_674)
      | ~ m1_subset_1(F_674,k1_zfmisc_1(k2_zfmisc_1(C_677,D_673)))
      | ~ v1_funct_1(F_674)
      | ~ m1_subset_1(E_675,k1_zfmisc_1(k2_zfmisc_1(A_672,B_676)))
      | ~ v1_funct_1(E_675) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_11713,plain,(
    ! [A_989,B_990,A_991,E_992] :
      ( k1_partfun1(A_989,B_990,A_991,A_991,E_992,k6_partfun1(A_991)) = k5_relat_1(E_992,k6_partfun1(A_991))
      | ~ v1_funct_1(k6_partfun1(A_991))
      | ~ m1_subset_1(E_992,k1_zfmisc_1(k2_zfmisc_1(A_989,B_990)))
      | ~ v1_funct_1(E_992) ) ),
    inference(resolution,[status(thm)],[c_68,c_8195])).

tff(c_11715,plain,(
    ! [A_989,B_990,E_992] :
      ( k1_partfun1(A_989,B_990,'#skF_1','#skF_1',E_992,k6_partfun1('#skF_1')) = k5_relat_1(E_992,k6_partfun1('#skF_1'))
      | ~ v1_funct_1('#skF_1')
      | ~ m1_subset_1(E_992,k1_zfmisc_1(k2_zfmisc_1(A_989,B_990)))
      | ~ v1_funct_1(E_992) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7661,c_11713])).

tff(c_13696,plain,(
    ! [A_1048,B_1049,E_1050] :
      ( k1_partfun1(A_1048,B_1049,'#skF_1','#skF_1',E_1050,'#skF_1') = k5_relat_1(E_1050,'#skF_1')
      | ~ m1_subset_1(E_1050,k1_zfmisc_1(k2_zfmisc_1(A_1048,B_1049)))
      | ~ v1_funct_1(E_1050) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7678,c_7661,c_7661,c_11715])).

tff(c_13713,plain,(
    ! [A_1051] :
      ( k1_partfun1(A_1051,A_1051,'#skF_1','#skF_1',k6_partfun1(A_1051),'#skF_1') = k5_relat_1(k6_partfun1(A_1051),'#skF_1')
      | ~ v1_funct_1(k6_partfun1(A_1051)) ) ),
    inference(resolution,[status(thm)],[c_68,c_13696])).

tff(c_13717,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k6_partfun1('#skF_1'),'#skF_1') = k5_relat_1(k6_partfun1('#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_7661,c_13713])).

tff(c_13721,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7678,c_9379,c_7661,c_7661,c_13717])).

tff(c_7670,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7633,c_7633,c_101])).

tff(c_7986,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7661,c_7670])).

tff(c_9289,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_1')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9287,c_7986])).

tff(c_9361,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9355,c_9289])).

tff(c_13722,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13721,c_9361])).

tff(c_13725,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10269,c_13722])).

tff(c_13726,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_15732,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15730,c_13726])).

tff(c_17391,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1(k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17173,c_15732])).

tff(c_17468,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k2_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_17391])).

tff(c_17471,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13758,c_84,c_15138,c_15579,c_14635,c_17468])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:40:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.48/4.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.54/4.16  
% 10.54/4.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.54/4.17  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 10.54/4.17  
% 10.54/4.17  %Foreground sorts:
% 10.54/4.17  
% 10.54/4.17  
% 10.54/4.17  %Background operators:
% 10.54/4.17  
% 10.54/4.17  
% 10.54/4.17  %Foreground operators:
% 10.54/4.17  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.54/4.17  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 10.54/4.17  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 10.54/4.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.54/4.17  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 10.54/4.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.54/4.17  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 10.54/4.17  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 10.54/4.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.54/4.17  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.54/4.17  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.54/4.17  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.54/4.17  tff('#skF_2', type, '#skF_2': $i).
% 10.54/4.17  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 10.54/4.17  tff('#skF_1', type, '#skF_1': $i).
% 10.54/4.17  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 10.54/4.17  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 10.54/4.17  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 10.54/4.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.54/4.17  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 10.54/4.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.54/4.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.54/4.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.54/4.17  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 10.54/4.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.54/4.17  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 10.54/4.17  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 10.54/4.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.54/4.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.54/4.17  
% 10.54/4.20  tff(f_174, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_funct_2)).
% 10.54/4.20  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 10.54/4.20  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 10.54/4.20  tff(f_139, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 10.54/4.20  tff(f_81, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 10.54/4.20  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 10.54/4.20  tff(f_119, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 10.54/4.20  tff(f_161, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 10.54/4.20  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 10.54/4.20  tff(f_159, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 10.54/4.20  tff(f_135, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 10.54/4.20  tff(f_149, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 10.54/4.20  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 10.54/4.20  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 10.54/4.20  tff(f_111, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 10.54/4.20  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 10.54/4.20  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 10.54/4.20  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 10.54/4.20  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.54/4.20  tff(c_78, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_174])).
% 10.54/4.20  tff(c_13745, plain, (![C_1059, A_1060, B_1061]: (v1_relat_1(C_1059) | ~m1_subset_1(C_1059, k1_zfmisc_1(k2_zfmisc_1(A_1060, B_1061))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.54/4.20  tff(c_13758, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_78, c_13745])).
% 10.54/4.20  tff(c_84, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_174])).
% 10.54/4.20  tff(c_80, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_174])).
% 10.54/4.20  tff(c_15120, plain, (![C_1208, A_1209, B_1210]: (v2_funct_1(C_1208) | ~v3_funct_2(C_1208, A_1209, B_1210) | ~v1_funct_1(C_1208) | ~m1_subset_1(C_1208, k1_zfmisc_1(k2_zfmisc_1(A_1209, B_1210))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.54/4.20  tff(c_15133, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_78, c_15120])).
% 10.54/4.20  tff(c_15138, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_15133])).
% 10.54/4.20  tff(c_68, plain, (![A_33]: (m1_subset_1(k6_partfun1(A_33), k1_zfmisc_1(k2_zfmisc_1(A_33, A_33))))), inference(cnfTransformation, [status(thm)], [f_139])).
% 10.54/4.20  tff(c_15329, plain, (![A_1237, B_1238, C_1239, D_1240]: (r2_relset_1(A_1237, B_1238, C_1239, C_1239) | ~m1_subset_1(D_1240, k1_zfmisc_1(k2_zfmisc_1(A_1237, B_1238))) | ~m1_subset_1(C_1239, k1_zfmisc_1(k2_zfmisc_1(A_1237, B_1238))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.54/4.20  tff(c_15567, plain, (![A_1265, C_1266]: (r2_relset_1(A_1265, A_1265, C_1266, C_1266) | ~m1_subset_1(C_1266, k1_zfmisc_1(k2_zfmisc_1(A_1265, A_1265))))), inference(resolution, [status(thm)], [c_68, c_15329])).
% 10.54/4.20  tff(c_15579, plain, (![A_33]: (r2_relset_1(A_33, A_33, k6_partfun1(A_33), k6_partfun1(A_33)))), inference(resolution, [status(thm)], [c_68, c_15567])).
% 10.54/4.20  tff(c_13828, plain, (![C_1069, B_1070, A_1071]: (v5_relat_1(C_1069, B_1070) | ~m1_subset_1(C_1069, k1_zfmisc_1(k2_zfmisc_1(A_1071, B_1070))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.54/4.20  tff(c_13841, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_78, c_13828])).
% 10.54/4.20  tff(c_14074, plain, (![B_1097, A_1098]: (k2_relat_1(B_1097)=A_1098 | ~v2_funct_2(B_1097, A_1098) | ~v5_relat_1(B_1097, A_1098) | ~v1_relat_1(B_1097))), inference(cnfTransformation, [status(thm)], [f_119])).
% 10.54/4.20  tff(c_14089, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_13841, c_14074])).
% 10.54/4.20  tff(c_14104, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_13758, c_14089])).
% 10.54/4.20  tff(c_14131, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_14104])).
% 10.54/4.20  tff(c_14614, plain, (![C_1159, B_1160, A_1161]: (v2_funct_2(C_1159, B_1160) | ~v3_funct_2(C_1159, A_1161, B_1160) | ~v1_funct_1(C_1159) | ~m1_subset_1(C_1159, k1_zfmisc_1(k2_zfmisc_1(A_1161, B_1160))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.54/4.20  tff(c_14627, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_78, c_14614])).
% 10.54/4.20  tff(c_14632, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_14627])).
% 10.54/4.20  tff(c_14634, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14131, c_14632])).
% 10.54/4.20  tff(c_14635, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_14104])).
% 10.54/4.20  tff(c_74, plain, (![A_42]: (k6_relat_1(A_42)=k6_partfun1(A_42))), inference(cnfTransformation, [status(thm)], [f_161])).
% 10.54/4.20  tff(c_22, plain, (![A_9]: (k5_relat_1(k2_funct_1(A_9), A_9)=k6_relat_1(k2_relat_1(A_9)) | ~v2_funct_1(A_9) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.54/4.20  tff(c_86, plain, (![A_9]: (k5_relat_1(k2_funct_1(A_9), A_9)=k6_partfun1(k2_relat_1(A_9)) | ~v2_funct_1(A_9) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_22])).
% 10.54/4.20  tff(c_82, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_174])).
% 10.54/4.20  tff(c_15711, plain, (![A_1279, B_1280]: (k2_funct_2(A_1279, B_1280)=k2_funct_1(B_1280) | ~m1_subset_1(B_1280, k1_zfmisc_1(k2_zfmisc_1(A_1279, A_1279))) | ~v3_funct_2(B_1280, A_1279, A_1279) | ~v1_funct_2(B_1280, A_1279, A_1279) | ~v1_funct_1(B_1280))), inference(cnfTransformation, [status(thm)], [f_159])).
% 10.54/4.20  tff(c_15725, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_78, c_15711])).
% 10.54/4.20  tff(c_15730, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_15725])).
% 10.54/4.20  tff(c_15651, plain, (![A_1274, B_1275]: (v1_funct_1(k2_funct_2(A_1274, B_1275)) | ~m1_subset_1(B_1275, k1_zfmisc_1(k2_zfmisc_1(A_1274, A_1274))) | ~v3_funct_2(B_1275, A_1274, A_1274) | ~v1_funct_2(B_1275, A_1274, A_1274) | ~v1_funct_1(B_1275))), inference(cnfTransformation, [status(thm)], [f_135])).
% 10.54/4.20  tff(c_15665, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_78, c_15651])).
% 10.54/4.20  tff(c_15670, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_15665])).
% 10.54/4.20  tff(c_15731, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_15730, c_15670])).
% 10.54/4.20  tff(c_58, plain, (![A_31, B_32]: (m1_subset_1(k2_funct_2(A_31, B_32), k1_zfmisc_1(k2_zfmisc_1(A_31, A_31))) | ~m1_subset_1(B_32, k1_zfmisc_1(k2_zfmisc_1(A_31, A_31))) | ~v3_funct_2(B_32, A_31, A_31) | ~v1_funct_2(B_32, A_31, A_31) | ~v1_funct_1(B_32))), inference(cnfTransformation, [status(thm)], [f_135])).
% 10.54/4.20  tff(c_16456, plain, (![B_1333, A_1329, F_1331, D_1330, C_1334, E_1332]: (k1_partfun1(A_1329, B_1333, C_1334, D_1330, E_1332, F_1331)=k5_relat_1(E_1332, F_1331) | ~m1_subset_1(F_1331, k1_zfmisc_1(k2_zfmisc_1(C_1334, D_1330))) | ~v1_funct_1(F_1331) | ~m1_subset_1(E_1332, k1_zfmisc_1(k2_zfmisc_1(A_1329, B_1333))) | ~v1_funct_1(E_1332))), inference(cnfTransformation, [status(thm)], [f_149])).
% 10.54/4.20  tff(c_16469, plain, (![A_1329, B_1333, E_1332]: (k1_partfun1(A_1329, B_1333, '#skF_1', '#skF_1', E_1332, '#skF_2')=k5_relat_1(E_1332, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_1332, k1_zfmisc_1(k2_zfmisc_1(A_1329, B_1333))) | ~v1_funct_1(E_1332))), inference(resolution, [status(thm)], [c_78, c_16456])).
% 10.54/4.20  tff(c_16483, plain, (![A_1335, B_1336, E_1337]: (k1_partfun1(A_1335, B_1336, '#skF_1', '#skF_1', E_1337, '#skF_2')=k5_relat_1(E_1337, '#skF_2') | ~m1_subset_1(E_1337, k1_zfmisc_1(k2_zfmisc_1(A_1335, B_1336))) | ~v1_funct_1(E_1337))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_16469])).
% 10.54/4.20  tff(c_17145, plain, (![A_1365, B_1366]: (k1_partfun1(A_1365, A_1365, '#skF_1', '#skF_1', k2_funct_2(A_1365, B_1366), '#skF_2')=k5_relat_1(k2_funct_2(A_1365, B_1366), '#skF_2') | ~v1_funct_1(k2_funct_2(A_1365, B_1366)) | ~m1_subset_1(B_1366, k1_zfmisc_1(k2_zfmisc_1(A_1365, A_1365))) | ~v3_funct_2(B_1366, A_1365, A_1365) | ~v1_funct_2(B_1366, A_1365, A_1365) | ~v1_funct_1(B_1366))), inference(resolution, [status(thm)], [c_58, c_16483])).
% 10.54/4.20  tff(c_17161, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2')=k5_relat_1(k2_funct_2('#skF_1', '#skF_2'), '#skF_2') | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_78, c_17145])).
% 10.54/4.20  tff(c_17173, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2')=k5_relat_1(k2_funct_1('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_15731, c_15730, c_15730, c_15730, c_17161])).
% 10.54/4.20  tff(c_7611, plain, (![C_628, B_629, A_630]: (v2_funct_2(C_628, B_629) | ~v3_funct_2(C_628, A_630, B_629) | ~v1_funct_1(C_628) | ~m1_subset_1(C_628, k1_zfmisc_1(k2_zfmisc_1(A_630, B_629))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.54/4.20  tff(c_7624, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_78, c_7611])).
% 10.54/4.20  tff(c_7629, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_7624])).
% 10.54/4.20  tff(c_148, plain, (![C_58, A_59, B_60]: (v1_relat_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.54/4.20  tff(c_161, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_78, c_148])).
% 10.54/4.20  tff(c_1257, plain, (![C_172, A_173, B_174]: (v2_funct_1(C_172) | ~v3_funct_2(C_172, A_173, B_174) | ~v1_funct_1(C_172) | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(A_173, B_174))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.54/4.20  tff(c_1270, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_78, c_1257])).
% 10.54/4.20  tff(c_1275, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_1270])).
% 10.54/4.20  tff(c_1705, plain, (![A_232, B_233, C_234, D_235]: (r2_relset_1(A_232, B_233, C_234, C_234) | ~m1_subset_1(D_235, k1_zfmisc_1(k2_zfmisc_1(A_232, B_233))) | ~m1_subset_1(C_234, k1_zfmisc_1(k2_zfmisc_1(A_232, B_233))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.54/4.20  tff(c_1719, plain, (![A_236, C_237]: (r2_relset_1(A_236, A_236, C_237, C_237) | ~m1_subset_1(C_237, k1_zfmisc_1(k2_zfmisc_1(A_236, A_236))))), inference(resolution, [status(thm)], [c_68, c_1705])).
% 10.54/4.20  tff(c_1731, plain, (![A_33]: (r2_relset_1(A_33, A_33, k6_partfun1(A_33), k6_partfun1(A_33)))), inference(resolution, [status(thm)], [c_68, c_1719])).
% 10.54/4.20  tff(c_259, plain, (![C_76, B_77, A_78]: (v5_relat_1(C_76, B_77) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_78, B_77))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.54/4.20  tff(c_272, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_78, c_259])).
% 10.54/4.20  tff(c_477, plain, (![B_99, A_100]: (k2_relat_1(B_99)=A_100 | ~v2_funct_2(B_99, A_100) | ~v5_relat_1(B_99, A_100) | ~v1_relat_1(B_99))), inference(cnfTransformation, [status(thm)], [f_119])).
% 10.54/4.20  tff(c_492, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_272, c_477])).
% 10.54/4.20  tff(c_507, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_161, c_492])).
% 10.54/4.20  tff(c_535, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_507])).
% 10.54/4.20  tff(c_919, plain, (![C_145, B_146, A_147]: (v2_funct_2(C_145, B_146) | ~v3_funct_2(C_145, A_147, B_146) | ~v1_funct_1(C_145) | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1(A_147, B_146))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.54/4.20  tff(c_932, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_78, c_919])).
% 10.54/4.20  tff(c_937, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_932])).
% 10.54/4.20  tff(c_939, plain, $false, inference(negUnitSimplification, [status(thm)], [c_535, c_937])).
% 10.54/4.20  tff(c_940, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_507])).
% 10.54/4.20  tff(c_18, plain, (![A_8]: (k2_relat_1(A_8)!=k1_xboole_0 | k1_xboole_0=A_8 | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.54/4.20  tff(c_168, plain, (k2_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_161, c_18])).
% 10.54/4.20  tff(c_179, plain, (k2_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_168])).
% 10.54/4.20  tff(c_942, plain, (k1_xboole_0!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_940, c_179])).
% 10.54/4.20  tff(c_1090, plain, (![A_159, B_160, C_161]: (k1_relset_1(A_159, B_160, C_161)=k1_relat_1(C_161) | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(A_159, B_160))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.54/4.20  tff(c_1107, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_78, c_1090])).
% 10.54/4.20  tff(c_1663, plain, (![B_228, A_229, C_230]: (k1_xboole_0=B_228 | k1_relset_1(A_229, B_228, C_230)=A_229 | ~v1_funct_2(C_230, A_229, B_228) | ~m1_subset_1(C_230, k1_zfmisc_1(k2_zfmisc_1(A_229, B_228))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 10.54/4.20  tff(c_1676, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_78, c_1663])).
% 10.54/4.20  tff(c_1683, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_1107, c_1676])).
% 10.54/4.20  tff(c_1684, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_942, c_1683])).
% 10.54/4.20  tff(c_24, plain, (![A_9]: (k5_relat_1(A_9, k2_funct_1(A_9))=k6_relat_1(k1_relat_1(A_9)) | ~v2_funct_1(A_9) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.54/4.20  tff(c_85, plain, (![A_9]: (k5_relat_1(A_9, k2_funct_1(A_9))=k6_partfun1(k1_relat_1(A_9)) | ~v2_funct_1(A_9) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_24])).
% 10.54/4.20  tff(c_1875, plain, (![A_252, B_253]: (k2_funct_2(A_252, B_253)=k2_funct_1(B_253) | ~m1_subset_1(B_253, k1_zfmisc_1(k2_zfmisc_1(A_252, A_252))) | ~v3_funct_2(B_253, A_252, A_252) | ~v1_funct_2(B_253, A_252, A_252) | ~v1_funct_1(B_253))), inference(cnfTransformation, [status(thm)], [f_159])).
% 10.54/4.20  tff(c_1889, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_78, c_1875])).
% 10.54/4.20  tff(c_1894, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_1889])).
% 10.54/4.20  tff(c_1743, plain, (![A_239, B_240]: (v1_funct_1(k2_funct_2(A_239, B_240)) | ~m1_subset_1(B_240, k1_zfmisc_1(k2_zfmisc_1(A_239, A_239))) | ~v3_funct_2(B_240, A_239, A_239) | ~v1_funct_2(B_240, A_239, A_239) | ~v1_funct_1(B_240))), inference(cnfTransformation, [status(thm)], [f_135])).
% 10.54/4.20  tff(c_1757, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_78, c_1743])).
% 10.54/4.20  tff(c_1762, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_1757])).
% 10.54/4.20  tff(c_1895, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1894, c_1762])).
% 10.54/4.20  tff(c_2159, plain, (![A_287, B_288]: (m1_subset_1(k2_funct_2(A_287, B_288), k1_zfmisc_1(k2_zfmisc_1(A_287, A_287))) | ~m1_subset_1(B_288, k1_zfmisc_1(k2_zfmisc_1(A_287, A_287))) | ~v3_funct_2(B_288, A_287, A_287) | ~v1_funct_2(B_288, A_287, A_287) | ~v1_funct_1(B_288))), inference(cnfTransformation, [status(thm)], [f_135])).
% 10.54/4.20  tff(c_2211, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1894, c_2159])).
% 10.54/4.20  tff(c_2236, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_78, c_2211])).
% 10.54/4.20  tff(c_10, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.54/4.20  tff(c_2310, plain, (r1_tarski(k2_funct_1('#skF_2'), k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_2236, c_10])).
% 10.54/4.20  tff(c_12, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.54/4.20  tff(c_2354, plain, (![B_293, A_289, E_292, D_290, C_294, F_291]: (k1_partfun1(A_289, B_293, C_294, D_290, E_292, F_291)=k5_relat_1(E_292, F_291) | ~m1_subset_1(F_291, k1_zfmisc_1(k2_zfmisc_1(C_294, D_290))) | ~v1_funct_1(F_291) | ~m1_subset_1(E_292, k1_zfmisc_1(k2_zfmisc_1(A_289, B_293))) | ~v1_funct_1(E_292))), inference(cnfTransformation, [status(thm)], [f_149])).
% 10.54/4.20  tff(c_5606, plain, (![B_453, C_450, A_455, D_454, A_452, E_451]: (k1_partfun1(A_452, B_453, C_450, D_454, E_451, A_455)=k5_relat_1(E_451, A_455) | ~v1_funct_1(A_455) | ~m1_subset_1(E_451, k1_zfmisc_1(k2_zfmisc_1(A_452, B_453))) | ~v1_funct_1(E_451) | ~r1_tarski(A_455, k2_zfmisc_1(C_450, D_454)))), inference(resolution, [status(thm)], [c_12, c_2354])).
% 10.54/4.20  tff(c_5625, plain, (![C_450, D_454, A_455]: (k1_partfun1('#skF_1', '#skF_1', C_450, D_454, '#skF_2', A_455)=k5_relat_1('#skF_2', A_455) | ~v1_funct_1(A_455) | ~v1_funct_1('#skF_2') | ~r1_tarski(A_455, k2_zfmisc_1(C_450, D_454)))), inference(resolution, [status(thm)], [c_78, c_5606])).
% 10.54/4.20  tff(c_5650, plain, (![C_456, D_457, A_458]: (k1_partfun1('#skF_1', '#skF_1', C_456, D_457, '#skF_2', A_458)=k5_relat_1('#skF_2', A_458) | ~v1_funct_1(A_458) | ~r1_tarski(A_458, k2_zfmisc_1(C_456, D_457)))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_5625])).
% 10.54/4.20  tff(c_5665, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_2310, c_5650])).
% 10.54/4.20  tff(c_5699, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1895, c_5665])).
% 10.54/4.20  tff(c_76, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1')) | ~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_174])).
% 10.54/4.20  tff(c_101, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(splitLeft, [status(thm)], [c_76])).
% 10.54/4.20  tff(c_1896, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1894, c_101])).
% 10.54/4.20  tff(c_6036, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_5699, c_1896])).
% 10.54/4.20  tff(c_6043, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k1_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_85, c_6036])).
% 10.54/4.20  tff(c_6046, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_161, c_84, c_1275, c_1731, c_1684, c_6043])).
% 10.54/4.20  tff(c_6047, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_168])).
% 10.54/4.20  tff(c_6048, plain, (k2_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_168])).
% 10.54/4.20  tff(c_6071, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_6047, c_6048])).
% 10.54/4.20  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.54/4.20  tff(c_6052, plain, (![A_3]: (r1_tarski('#skF_2', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_6047, c_8])).
% 10.54/4.20  tff(c_6113, plain, (![B_475, A_476]: (v5_relat_1(B_475, A_476) | ~r1_tarski(k2_relat_1(B_475), A_476) | ~v1_relat_1(B_475))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.54/4.20  tff(c_6116, plain, (![A_476]: (v5_relat_1('#skF_2', A_476) | ~r1_tarski('#skF_2', A_476) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_6071, c_6113])).
% 10.54/4.20  tff(c_6122, plain, (![A_476]: (v5_relat_1('#skF_2', A_476))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_6052, c_6116])).
% 10.54/4.20  tff(c_6351, plain, (![B_504, A_505]: (k2_relat_1(B_504)=A_505 | ~v2_funct_2(B_504, A_505) | ~v5_relat_1(B_504, A_505) | ~v1_relat_1(B_504))), inference(cnfTransformation, [status(thm)], [f_119])).
% 10.54/4.20  tff(c_6363, plain, (![A_476]: (k2_relat_1('#skF_2')=A_476 | ~v2_funct_2('#skF_2', A_476) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_6122, c_6351])).
% 10.54/4.20  tff(c_6374, plain, (![A_476]: (A_476='#skF_2' | ~v2_funct_2('#skF_2', A_476))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_6071, c_6363])).
% 10.54/4.20  tff(c_7633, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_7629, c_6374])).
% 10.54/4.20  tff(c_7671, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_7633, c_6052])).
% 10.54/4.20  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.54/4.20  tff(c_7899, plain, (![A_641, B_642, C_643, D_644]: (r2_relset_1(A_641, B_642, C_643, C_643) | ~m1_subset_1(D_644, k1_zfmisc_1(k2_zfmisc_1(A_641, B_642))) | ~m1_subset_1(C_643, k1_zfmisc_1(k2_zfmisc_1(A_641, B_642))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.54/4.20  tff(c_8946, plain, (![A_768, B_769, C_770, A_771]: (r2_relset_1(A_768, B_769, C_770, C_770) | ~m1_subset_1(C_770, k1_zfmisc_1(k2_zfmisc_1(A_768, B_769))) | ~r1_tarski(A_771, k2_zfmisc_1(A_768, B_769)))), inference(resolution, [status(thm)], [c_12, c_7899])).
% 10.54/4.20  tff(c_10238, plain, (![A_874, B_875, A_876, A_877]: (r2_relset_1(A_874, B_875, A_876, A_876) | ~r1_tarski(A_877, k2_zfmisc_1(A_874, B_875)) | ~r1_tarski(A_876, k2_zfmisc_1(A_874, B_875)))), inference(resolution, [status(thm)], [c_12, c_8946])).
% 10.54/4.20  tff(c_10255, plain, (![A_878, B_879, A_880]: (r2_relset_1(A_878, B_879, A_880, A_880) | ~r1_tarski(A_880, k2_zfmisc_1(A_878, B_879)))), inference(resolution, [status(thm)], [c_6, c_10238])).
% 10.54/4.20  tff(c_10269, plain, (![A_878, B_879]: (r2_relset_1(A_878, B_879, '#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_7671, c_10255])).
% 10.54/4.20  tff(c_7678, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7633, c_84])).
% 10.54/4.20  tff(c_7674, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7633, c_161])).
% 10.54/4.20  tff(c_6712, plain, (![C_537, A_538, B_539]: (v2_funct_1(C_537) | ~v3_funct_2(C_537, A_538, B_539) | ~v1_funct_1(C_537) | ~m1_subset_1(C_537, k1_zfmisc_1(k2_zfmisc_1(A_538, B_539))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.54/4.20  tff(c_6725, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_78, c_6712])).
% 10.54/4.20  tff(c_6730, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_6725])).
% 10.54/4.20  tff(c_7645, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7633, c_6730])).
% 10.54/4.20  tff(c_160, plain, (![A_33]: (v1_relat_1(k6_partfun1(A_33)))), inference(resolution, [status(thm)], [c_68, c_148])).
% 10.54/4.20  tff(c_6182, plain, (![C_488, B_489, A_490]: (v5_relat_1(C_488, B_489) | ~m1_subset_1(C_488, k1_zfmisc_1(k2_zfmisc_1(A_490, B_489))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.54/4.20  tff(c_6194, plain, (![A_33]: (v5_relat_1(k6_partfun1(A_33), A_33))), inference(resolution, [status(thm)], [c_68, c_6182])).
% 10.54/4.20  tff(c_6201, plain, (![B_495, A_496]: (r1_tarski(k2_relat_1(B_495), A_496) | ~v5_relat_1(B_495, A_496) | ~v1_relat_1(B_495))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.54/4.20  tff(c_118, plain, (![B_54, A_55]: (B_54=A_55 | ~r1_tarski(B_54, A_55) | ~r1_tarski(A_55, B_54))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.54/4.20  tff(c_130, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_118])).
% 10.54/4.20  tff(c_6049, plain, (![A_3]: (A_3='#skF_2' | ~r1_tarski(A_3, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_6047, c_6047, c_130])).
% 10.54/4.20  tff(c_6252, plain, (![B_502]: (k2_relat_1(B_502)='#skF_2' | ~v5_relat_1(B_502, '#skF_2') | ~v1_relat_1(B_502))), inference(resolution, [status(thm)], [c_6201, c_6049])).
% 10.54/4.20  tff(c_6260, plain, (k2_relat_1(k6_partfun1('#skF_2'))='#skF_2' | ~v1_relat_1(k6_partfun1('#skF_2'))), inference(resolution, [status(thm)], [c_6194, c_6252])).
% 10.54/4.20  tff(c_6270, plain, (k2_relat_1(k6_partfun1('#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_160, c_6260])).
% 10.54/4.20  tff(c_170, plain, (![A_61]: (v1_relat_1(k6_partfun1(A_61)))), inference(resolution, [status(thm)], [c_68, c_148])).
% 10.54/4.20  tff(c_177, plain, (![A_61]: (k2_relat_1(k6_partfun1(A_61))!=k1_xboole_0 | k6_partfun1(A_61)=k1_xboole_0)), inference(resolution, [status(thm)], [c_170, c_18])).
% 10.54/4.20  tff(c_6132, plain, (![A_61]: (k2_relat_1(k6_partfun1(A_61))!='#skF_2' | k6_partfun1(A_61)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6047, c_6047, c_177])).
% 10.54/4.20  tff(c_6291, plain, (k6_partfun1('#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_6270, c_6132])).
% 10.54/4.20  tff(c_7661, plain, (k6_partfun1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_7633, c_7633, c_6291])).
% 10.54/4.20  tff(c_7672, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_7633, c_7633, c_6071])).
% 10.54/4.20  tff(c_7677, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7633, c_82])).
% 10.54/4.20  tff(c_7676, plain, (v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7633, c_80])).
% 10.54/4.20  tff(c_6096, plain, (![A_472, A_473, B_474]: (v1_relat_1(A_472) | ~r1_tarski(A_472, k2_zfmisc_1(A_473, B_474)))), inference(resolution, [status(thm)], [c_12, c_148])).
% 10.54/4.20  tff(c_6112, plain, (![A_473, B_474]: (v1_relat_1(k2_zfmisc_1(A_473, B_474)))), inference(resolution, [status(thm)], [c_6, c_6096])).
% 10.54/4.20  tff(c_6229, plain, (![A_497, B_498, A_499]: (v5_relat_1(A_497, B_498) | ~r1_tarski(A_497, k2_zfmisc_1(A_499, B_498)))), inference(resolution, [status(thm)], [c_12, c_6182])).
% 10.54/4.20  tff(c_6250, plain, (![A_499, B_498]: (v5_relat_1(k2_zfmisc_1(A_499, B_498), B_498))), inference(resolution, [status(thm)], [c_6, c_6229])).
% 10.54/4.20  tff(c_6256, plain, (![A_499]: (k2_relat_1(k2_zfmisc_1(A_499, '#skF_2'))='#skF_2' | ~v1_relat_1(k2_zfmisc_1(A_499, '#skF_2')))), inference(resolution, [status(thm)], [c_6250, c_6252])).
% 10.54/4.20  tff(c_6267, plain, (![A_499]: (k2_relat_1(k2_zfmisc_1(A_499, '#skF_2'))='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6112, c_6256])).
% 10.54/4.20  tff(c_6150, plain, (![A_484]: (k2_relat_1(A_484)!='#skF_2' | A_484='#skF_2' | ~v1_relat_1(A_484))), inference(demodulation, [status(thm), theory('equality')], [c_6047, c_6047, c_18])).
% 10.54/4.20  tff(c_6545, plain, (![A_522, B_523]: (k2_relat_1(k2_zfmisc_1(A_522, B_523))!='#skF_2' | k2_zfmisc_1(A_522, B_523)='#skF_2')), inference(resolution, [status(thm)], [c_6112, c_6150])).
% 10.54/4.20  tff(c_6549, plain, (![A_499]: (k2_zfmisc_1(A_499, '#skF_2')='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6267, c_6545])).
% 10.54/4.20  tff(c_6319, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_6291, c_68])).
% 10.54/4.20  tff(c_6551, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_6549, c_6319])).
% 10.54/4.20  tff(c_7654, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_7633, c_7633, c_6551])).
% 10.54/4.20  tff(c_7655, plain, (![A_499]: (k2_zfmisc_1(A_499, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7633, c_7633, c_6549])).
% 10.54/4.20  tff(c_8000, plain, (![A_655, B_656]: (k2_funct_2(A_655, B_656)=k2_funct_1(B_656) | ~m1_subset_1(B_656, k1_zfmisc_1(k2_zfmisc_1(A_655, A_655))) | ~v3_funct_2(B_656, A_655, A_655) | ~v1_funct_2(B_656, A_655, A_655) | ~v1_funct_1(B_656))), inference(cnfTransformation, [status(thm)], [f_159])).
% 10.54/4.20  tff(c_9282, plain, (![A_813]: (k2_funct_2(A_813, k6_partfun1(A_813))=k2_funct_1(k6_partfun1(A_813)) | ~v3_funct_2(k6_partfun1(A_813), A_813, A_813) | ~v1_funct_2(k6_partfun1(A_813), A_813, A_813) | ~v1_funct_1(k6_partfun1(A_813)))), inference(resolution, [status(thm)], [c_68, c_8000])).
% 10.54/4.20  tff(c_9285, plain, (k2_funct_2('#skF_1', k6_partfun1('#skF_1'))=k2_funct_1(k6_partfun1('#skF_1')) | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2(k6_partfun1('#skF_1'), '#skF_1', '#skF_1') | ~v1_funct_1(k6_partfun1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_7661, c_9282])).
% 10.54/4.20  tff(c_9287, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7678, c_7661, c_7677, c_7661, c_7676, c_7661, c_7661, c_9285])).
% 10.54/4.20  tff(c_9293, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_9287, c_58])).
% 10.54/4.20  tff(c_9297, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_7678, c_7677, c_7676, c_7654, c_7655, c_7655, c_9293])).
% 10.54/4.20  tff(c_9327, plain, (r1_tarski(k2_funct_1('#skF_1'), '#skF_1')), inference(resolution, [status(thm)], [c_9297, c_10])).
% 10.54/4.20  tff(c_7669, plain, (![A_3]: (A_3='#skF_1' | ~r1_tarski(A_3, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_7633, c_7633, c_6049])).
% 10.54/4.20  tff(c_9355, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_9327, c_7669])).
% 10.54/4.20  tff(c_9372, plain, (k6_partfun1(k2_relat_1('#skF_1'))=k5_relat_1('#skF_1', '#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_9355, c_86])).
% 10.54/4.20  tff(c_9379, plain, (k5_relat_1('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_7674, c_7678, c_7645, c_7661, c_7672, c_9372])).
% 10.54/4.20  tff(c_8195, plain, (![C_677, F_674, A_672, B_676, D_673, E_675]: (k1_partfun1(A_672, B_676, C_677, D_673, E_675, F_674)=k5_relat_1(E_675, F_674) | ~m1_subset_1(F_674, k1_zfmisc_1(k2_zfmisc_1(C_677, D_673))) | ~v1_funct_1(F_674) | ~m1_subset_1(E_675, k1_zfmisc_1(k2_zfmisc_1(A_672, B_676))) | ~v1_funct_1(E_675))), inference(cnfTransformation, [status(thm)], [f_149])).
% 10.54/4.20  tff(c_11713, plain, (![A_989, B_990, A_991, E_992]: (k1_partfun1(A_989, B_990, A_991, A_991, E_992, k6_partfun1(A_991))=k5_relat_1(E_992, k6_partfun1(A_991)) | ~v1_funct_1(k6_partfun1(A_991)) | ~m1_subset_1(E_992, k1_zfmisc_1(k2_zfmisc_1(A_989, B_990))) | ~v1_funct_1(E_992))), inference(resolution, [status(thm)], [c_68, c_8195])).
% 10.54/4.20  tff(c_11715, plain, (![A_989, B_990, E_992]: (k1_partfun1(A_989, B_990, '#skF_1', '#skF_1', E_992, k6_partfun1('#skF_1'))=k5_relat_1(E_992, k6_partfun1('#skF_1')) | ~v1_funct_1('#skF_1') | ~m1_subset_1(E_992, k1_zfmisc_1(k2_zfmisc_1(A_989, B_990))) | ~v1_funct_1(E_992))), inference(superposition, [status(thm), theory('equality')], [c_7661, c_11713])).
% 10.54/4.20  tff(c_13696, plain, (![A_1048, B_1049, E_1050]: (k1_partfun1(A_1048, B_1049, '#skF_1', '#skF_1', E_1050, '#skF_1')=k5_relat_1(E_1050, '#skF_1') | ~m1_subset_1(E_1050, k1_zfmisc_1(k2_zfmisc_1(A_1048, B_1049))) | ~v1_funct_1(E_1050))), inference(demodulation, [status(thm), theory('equality')], [c_7678, c_7661, c_7661, c_11715])).
% 10.54/4.20  tff(c_13713, plain, (![A_1051]: (k1_partfun1(A_1051, A_1051, '#skF_1', '#skF_1', k6_partfun1(A_1051), '#skF_1')=k5_relat_1(k6_partfun1(A_1051), '#skF_1') | ~v1_funct_1(k6_partfun1(A_1051)))), inference(resolution, [status(thm)], [c_68, c_13696])).
% 10.54/4.20  tff(c_13717, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k6_partfun1('#skF_1'), '#skF_1')=k5_relat_1(k6_partfun1('#skF_1'), '#skF_1') | ~v1_funct_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_7661, c_13713])).
% 10.54/4.20  tff(c_13721, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_7678, c_9379, c_7661, c_7661, c_13717])).
% 10.54/4.20  tff(c_7670, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_7633, c_7633, c_101])).
% 10.54/4.20  tff(c_7986, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7661, c_7670])).
% 10.54/4.20  tff(c_9289, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_1')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9287, c_7986])).
% 10.54/4.20  tff(c_9361, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9355, c_9289])).
% 10.54/4.20  tff(c_13722, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_13721, c_9361])).
% 10.54/4.20  tff(c_13725, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10269, c_13722])).
% 10.54/4.20  tff(c_13726, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(splitRight, [status(thm)], [c_76])).
% 10.54/4.20  tff(c_15732, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_15730, c_13726])).
% 10.54/4.20  tff(c_17391, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1(k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_17173, c_15732])).
% 10.54/4.20  tff(c_17468, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k2_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_86, c_17391])).
% 10.54/4.20  tff(c_17471, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13758, c_84, c_15138, c_15579, c_14635, c_17468])).
% 10.54/4.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.54/4.20  
% 10.54/4.20  Inference rules
% 10.54/4.20  ----------------------
% 10.54/4.20  #Ref     : 0
% 10.54/4.20  #Sup     : 3509
% 10.54/4.20  #Fact    : 0
% 10.54/4.20  #Define  : 0
% 10.54/4.20  #Split   : 39
% 10.54/4.20  #Chain   : 0
% 10.54/4.20  #Close   : 0
% 10.54/4.20  
% 10.54/4.20  Ordering : KBO
% 10.54/4.20  
% 10.54/4.20  Simplification rules
% 10.54/4.20  ----------------------
% 10.54/4.20  #Subsume      : 515
% 10.54/4.20  #Demod        : 5362
% 10.54/4.20  #Tautology    : 1589
% 10.54/4.20  #SimpNegUnit  : 92
% 10.54/4.20  #BackRed      : 172
% 10.54/4.20  
% 10.54/4.20  #Partial instantiations: 0
% 10.54/4.20  #Strategies tried      : 1
% 10.54/4.20  
% 10.54/4.20  Timing (in seconds)
% 10.54/4.20  ----------------------
% 10.54/4.20  Preprocessing        : 0.38
% 10.54/4.20  Parsing              : 0.21
% 10.54/4.20  CNF conversion       : 0.02
% 10.54/4.20  Main loop            : 2.98
% 10.54/4.20  Inferencing          : 0.90
% 10.54/4.20  Reduction            : 1.20
% 10.54/4.20  Demodulation         : 0.89
% 10.54/4.20  BG Simplification    : 0.08
% 10.54/4.20  Subsumption          : 0.60
% 10.54/4.20  Abstraction          : 0.10
% 10.54/4.20  MUC search           : 0.00
% 10.54/4.20  Cooper               : 0.00
% 10.54/4.20  Total                : 3.44
% 10.54/4.20  Index Insertion      : 0.00
% 10.54/4.20  Index Deletion       : 0.00
% 10.54/4.20  Index Matching       : 0.00
% 10.54/4.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
