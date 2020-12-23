%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:02 EST 2020

% Result     : Theorem 14.16s
% Output     : CNFRefutation 14.43s
% Verified   : 
% Statistics : Number of formulae       :  258 (2079 expanded)
%              Number of leaves         :   48 ( 727 expanded)
%              Depth                    :   15
%              Number of atoms          :  540 (5692 expanded)
%              Number of equality atoms :  157 (1374 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_183,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_133,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_148,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
      & v1_relat_1(B)
      & v4_relat_1(B,A)
      & v5_relat_1(B,A)
      & v1_funct_1(B)
      & v1_funct_2(B,A,A)
      & v3_funct_2(B,A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_funct_2)).

tff(f_75,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_113,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_170,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_55,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_168,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_129,axiom,(
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

tff(f_158,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_45,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_105,axiom,(
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

tff(f_27,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_84,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_19343,plain,(
    ! [C_1156,A_1157,B_1158] :
      ( v1_relat_1(C_1156)
      | ~ m1_subset_1(C_1156,k1_zfmisc_1(k2_zfmisc_1(A_1157,B_1158))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_19361,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_19343])).

tff(c_90,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_86,plain,(
    v3_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_19816,plain,(
    ! [C_1223,A_1224,B_1225] :
      ( v2_funct_1(C_1223)
      | ~ v3_funct_2(C_1223,A_1224,B_1225)
      | ~ v1_funct_1(C_1223)
      | ~ m1_subset_1(C_1223,k1_zfmisc_1(k2_zfmisc_1(A_1224,B_1225))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_19829,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_19816])).

tff(c_19837,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_86,c_19829])).

tff(c_60,plain,(
    ! [A_31] : m1_subset_1(k6_partfun1(A_31),k1_zfmisc_1(k2_zfmisc_1(A_31,A_31))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_74,plain,(
    ! [A_32] : m1_subset_1('#skF_1'(A_32),k1_zfmisc_1(k2_zfmisc_1(A_32,A_32))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_20275,plain,(
    ! [A_1260,B_1261,C_1262,D_1263] :
      ( r2_relset_1(A_1260,B_1261,C_1262,C_1262)
      | ~ m1_subset_1(D_1263,k1_zfmisc_1(k2_zfmisc_1(A_1260,B_1261)))
      | ~ m1_subset_1(C_1262,k1_zfmisc_1(k2_zfmisc_1(A_1260,B_1261))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_20691,plain,(
    ! [A_1297,C_1298] :
      ( r2_relset_1(A_1297,A_1297,C_1298,C_1298)
      | ~ m1_subset_1(C_1298,k1_zfmisc_1(k2_zfmisc_1(A_1297,A_1297))) ) ),
    inference(resolution,[status(thm)],[c_74,c_20275])).

tff(c_20701,plain,(
    ! [A_31] : r2_relset_1(A_31,A_31,k6_partfun1(A_31),k6_partfun1(A_31)) ),
    inference(resolution,[status(thm)],[c_60,c_20691])).

tff(c_19391,plain,(
    ! [C_1160,B_1161,A_1162] :
      ( v5_relat_1(C_1160,B_1161)
      | ~ m1_subset_1(C_1160,k1_zfmisc_1(k2_zfmisc_1(A_1162,B_1161))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_19409,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_84,c_19391])).

tff(c_19529,plain,(
    ! [B_1187,A_1188] :
      ( k2_relat_1(B_1187) = A_1188
      | ~ v2_funct_2(B_1187,A_1188)
      | ~ v5_relat_1(B_1187,A_1188)
      | ~ v1_relat_1(B_1187) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_19535,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_19409,c_19529])).

tff(c_19547,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19361,c_19535])).

tff(c_19559,plain,(
    ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_19547])).

tff(c_19684,plain,(
    ! [C_1208,B_1209,A_1210] :
      ( v2_funct_2(C_1208,B_1209)
      | ~ v3_funct_2(C_1208,A_1210,B_1209)
      | ~ v1_funct_1(C_1208)
      | ~ m1_subset_1(C_1208,k1_zfmisc_1(k2_zfmisc_1(A_1210,B_1209))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_19697,plain,
    ( v2_funct_2('#skF_3','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_19684])).

tff(c_19706,plain,(
    v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_86,c_19697])).

tff(c_19708,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19559,c_19706])).

tff(c_19709,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_19547])).

tff(c_80,plain,(
    ! [A_42] : k6_relat_1(A_42) = k6_partfun1(A_42) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_14,plain,(
    ! [A_7] :
      ( k5_relat_1(k2_funct_1(A_7),A_7) = k6_relat_1(k2_relat_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_92,plain,(
    ! [A_7] :
      ( k5_relat_1(k2_funct_1(A_7),A_7) = k6_partfun1(k2_relat_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_14])).

tff(c_88,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_20546,plain,(
    ! [A_1288,B_1289] :
      ( k2_funct_2(A_1288,B_1289) = k2_funct_1(B_1289)
      | ~ m1_subset_1(B_1289,k1_zfmisc_1(k2_zfmisc_1(A_1288,A_1288)))
      | ~ v3_funct_2(B_1289,A_1288,A_1288)
      | ~ v1_funct_2(B_1289,A_1288,A_1288)
      | ~ v1_funct_1(B_1289) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_20559,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_20546])).

tff(c_20569,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_20559])).

tff(c_20516,plain,(
    ! [A_1284,B_1285] :
      ( v1_funct_1(k2_funct_2(A_1284,B_1285))
      | ~ m1_subset_1(B_1285,k1_zfmisc_1(k2_zfmisc_1(A_1284,A_1284)))
      | ~ v3_funct_2(B_1285,A_1284,A_1284)
      | ~ v1_funct_2(B_1285,A_1284,A_1284)
      | ~ v1_funct_1(B_1285) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_20529,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_20516])).

tff(c_20539,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_20529])).

tff(c_20570,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20569,c_20539])).

tff(c_50,plain,(
    ! [A_29,B_30] :
      ( m1_subset_1(k2_funct_2(A_29,B_30),k1_zfmisc_1(k2_zfmisc_1(A_29,A_29)))
      | ~ m1_subset_1(B_30,k1_zfmisc_1(k2_zfmisc_1(A_29,A_29)))
      | ~ v3_funct_2(B_30,A_29,A_29)
      | ~ v1_funct_2(B_30,A_29,A_29)
      | ~ v1_funct_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_20975,plain,(
    ! [A_1316,E_1319,F_1318,C_1321,B_1320,D_1317] :
      ( k1_partfun1(A_1316,B_1320,C_1321,D_1317,E_1319,F_1318) = k5_relat_1(E_1319,F_1318)
      | ~ m1_subset_1(F_1318,k1_zfmisc_1(k2_zfmisc_1(C_1321,D_1317)))
      | ~ v1_funct_1(F_1318)
      | ~ m1_subset_1(E_1319,k1_zfmisc_1(k2_zfmisc_1(A_1316,B_1320)))
      | ~ v1_funct_1(E_1319) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_20988,plain,(
    ! [A_1316,B_1320,E_1319] :
      ( k1_partfun1(A_1316,B_1320,'#skF_2','#skF_2',E_1319,'#skF_3') = k5_relat_1(E_1319,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_1319,k1_zfmisc_1(k2_zfmisc_1(A_1316,B_1320)))
      | ~ v1_funct_1(E_1319) ) ),
    inference(resolution,[status(thm)],[c_84,c_20975])).

tff(c_21018,plain,(
    ! [A_1322,B_1323,E_1324] :
      ( k1_partfun1(A_1322,B_1323,'#skF_2','#skF_2',E_1324,'#skF_3') = k5_relat_1(E_1324,'#skF_3')
      | ~ m1_subset_1(E_1324,k1_zfmisc_1(k2_zfmisc_1(A_1322,B_1323)))
      | ~ v1_funct_1(E_1324) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_20988])).

tff(c_21315,plain,(
    ! [A_1339,B_1340] :
      ( k1_partfun1(A_1339,A_1339,'#skF_2','#skF_2',k2_funct_2(A_1339,B_1340),'#skF_3') = k5_relat_1(k2_funct_2(A_1339,B_1340),'#skF_3')
      | ~ v1_funct_1(k2_funct_2(A_1339,B_1340))
      | ~ m1_subset_1(B_1340,k1_zfmisc_1(k2_zfmisc_1(A_1339,A_1339)))
      | ~ v3_funct_2(B_1340,A_1339,A_1339)
      | ~ v1_funct_2(B_1340,A_1339,A_1339)
      | ~ v1_funct_1(B_1340) ) ),
    inference(resolution,[status(thm)],[c_50,c_21018])).

tff(c_21330,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3') = k5_relat_1(k2_funct_2('#skF_2','#skF_3'),'#skF_3')
    | ~ v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_21315])).

tff(c_21347,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_20570,c_20569,c_20569,c_20569,c_21330])).

tff(c_148,plain,(
    ! [C_61,A_62,B_63] :
      ( v1_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_166,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_148])).

tff(c_782,plain,(
    ! [C_133,A_134,B_135] :
      ( v2_funct_1(C_133)
      | ~ v3_funct_2(C_133,A_134,B_135)
      | ~ v1_funct_1(C_133)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_795,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_782])).

tff(c_803,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_86,c_795])).

tff(c_1245,plain,(
    ! [A_169,B_170,C_171,D_172] :
      ( r2_relset_1(A_169,B_170,C_171,C_171)
      | ~ m1_subset_1(D_172,k1_zfmisc_1(k2_zfmisc_1(A_169,B_170)))
      | ~ m1_subset_1(C_171,k1_zfmisc_1(k2_zfmisc_1(A_169,B_170))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1258,plain,(
    ! [A_173,C_174] :
      ( r2_relset_1(A_173,A_173,C_174,C_174)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(A_173,A_173))) ) ),
    inference(resolution,[status(thm)],[c_60,c_1245])).

tff(c_1268,plain,(
    ! [A_31] : r2_relset_1(A_31,A_31,k6_partfun1(A_31),k6_partfun1(A_31)) ),
    inference(resolution,[status(thm)],[c_60,c_1258])).

tff(c_12,plain,(
    ! [A_6] : k2_relat_1(k6_relat_1(A_6)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_93,plain,(
    ! [A_6] : k2_relat_1(k6_partfun1(A_6)) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_12])).

tff(c_204,plain,(
    ! [A_67] : v1_relat_1(k6_partfun1(A_67)) ),
    inference(resolution,[status(thm)],[c_60,c_148])).

tff(c_6,plain,(
    ! [A_5] :
      ( k2_relat_1(A_5) != k1_xboole_0
      | k1_xboole_0 = A_5
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_210,plain,(
    ! [A_67] :
      ( k2_relat_1(k6_partfun1(A_67)) != k1_xboole_0
      | k6_partfun1(A_67) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_204,c_6])).

tff(c_214,plain,(
    ! [A_67] :
      ( k1_xboole_0 != A_67
      | k6_partfun1(A_67) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_210])).

tff(c_82,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2'))
    | ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_140,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_275,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k1_xboole_0)
    | k1_xboole_0 != '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_140])).

tff(c_311,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_275])).

tff(c_687,plain,(
    ! [A_119,B_120,C_121] :
      ( k1_relset_1(A_119,B_120,C_121) = k1_relat_1(C_121)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_706,plain,(
    k1_relset_1('#skF_2','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_687])).

tff(c_1128,plain,(
    ! [B_154,A_155,C_156] :
      ( k1_xboole_0 = B_154
      | k1_relset_1(A_155,B_154,C_156) = A_155
      | ~ v1_funct_2(C_156,A_155,B_154)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(k2_zfmisc_1(A_155,B_154))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1141,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_2','#skF_2','#skF_3') = '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_84,c_1128])).

tff(c_1151,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_706,c_1141])).

tff(c_1152,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_311,c_1151])).

tff(c_16,plain,(
    ! [A_7] :
      ( k5_relat_1(A_7,k2_funct_1(A_7)) = k6_relat_1(k1_relat_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_91,plain,(
    ! [A_7] :
      ( k5_relat_1(A_7,k2_funct_1(A_7)) = k6_partfun1(k1_relat_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_16])).

tff(c_1335,plain,(
    ! [A_185,B_186] :
      ( k2_funct_2(A_185,B_186) = k2_funct_1(B_186)
      | ~ m1_subset_1(B_186,k1_zfmisc_1(k2_zfmisc_1(A_185,A_185)))
      | ~ v3_funct_2(B_186,A_185,A_185)
      | ~ v1_funct_2(B_186,A_185,A_185)
      | ~ v1_funct_1(B_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_1348,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_1335])).

tff(c_1358,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_1348])).

tff(c_1305,plain,(
    ! [A_181,B_182] :
      ( v1_funct_1(k2_funct_2(A_181,B_182))
      | ~ m1_subset_1(B_182,k1_zfmisc_1(k2_zfmisc_1(A_181,A_181)))
      | ~ v3_funct_2(B_182,A_181,A_181)
      | ~ v1_funct_2(B_182,A_181,A_181)
      | ~ v1_funct_1(B_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1318,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_1305])).

tff(c_1328,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_1318])).

tff(c_1359,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1358,c_1328])).

tff(c_1743,plain,(
    ! [F_214,C_217,B_216,D_213,A_212,E_215] :
      ( k1_partfun1(A_212,B_216,C_217,D_213,E_215,F_214) = k5_relat_1(E_215,F_214)
      | ~ m1_subset_1(F_214,k1_zfmisc_1(k2_zfmisc_1(C_217,D_213)))
      | ~ v1_funct_1(F_214)
      | ~ m1_subset_1(E_215,k1_zfmisc_1(k2_zfmisc_1(A_212,B_216)))
      | ~ v1_funct_1(E_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_7869,plain,(
    ! [E_521,B_519,A_518,A_520,B_517] :
      ( k1_partfun1(A_518,B_517,A_520,A_520,E_521,k2_funct_2(A_520,B_519)) = k5_relat_1(E_521,k2_funct_2(A_520,B_519))
      | ~ v1_funct_1(k2_funct_2(A_520,B_519))
      | ~ m1_subset_1(E_521,k1_zfmisc_1(k2_zfmisc_1(A_518,B_517)))
      | ~ v1_funct_1(E_521)
      | ~ m1_subset_1(B_519,k1_zfmisc_1(k2_zfmisc_1(A_520,A_520)))
      | ~ v3_funct_2(B_519,A_520,A_520)
      | ~ v1_funct_2(B_519,A_520,A_520)
      | ~ v1_funct_1(B_519) ) ),
    inference(resolution,[status(thm)],[c_50,c_1743])).

tff(c_7892,plain,(
    ! [A_520,B_519] :
      ( k1_partfun1('#skF_2','#skF_2',A_520,A_520,'#skF_3',k2_funct_2(A_520,B_519)) = k5_relat_1('#skF_3',k2_funct_2(A_520,B_519))
      | ~ v1_funct_1(k2_funct_2(A_520,B_519))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(B_519,k1_zfmisc_1(k2_zfmisc_1(A_520,A_520)))
      | ~ v3_funct_2(B_519,A_520,A_520)
      | ~ v1_funct_2(B_519,A_520,A_520)
      | ~ v1_funct_1(B_519) ) ),
    inference(resolution,[status(thm)],[c_84,c_7869])).

tff(c_7979,plain,(
    ! [A_525,B_526] :
      ( k1_partfun1('#skF_2','#skF_2',A_525,A_525,'#skF_3',k2_funct_2(A_525,B_526)) = k5_relat_1('#skF_3',k2_funct_2(A_525,B_526))
      | ~ v1_funct_1(k2_funct_2(A_525,B_526))
      | ~ m1_subset_1(B_526,k1_zfmisc_1(k2_zfmisc_1(A_525,A_525)))
      | ~ v3_funct_2(B_526,A_525,A_525)
      | ~ v1_funct_2(B_526,A_525,A_525)
      | ~ v1_funct_1(B_526) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_7892])).

tff(c_8002,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')) = k5_relat_1('#skF_3',k2_funct_2('#skF_2','#skF_3'))
    | ~ v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_7979])).

tff(c_8029,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_1359,c_1358,c_1358,c_1358,c_8002])).

tff(c_1360,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1358,c_140])).

tff(c_8187,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k5_relat_1('#skF_3',k2_funct_1('#skF_3')),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8029,c_1360])).

tff(c_8194,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1(k1_relat_1('#skF_3')),k6_partfun1('#skF_2'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_8187])).

tff(c_8200,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_90,c_803,c_1268,c_1152,c_8194])).

tff(c_8202,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_275])).

tff(c_203,plain,
    ( k2_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_166,c_6])).

tff(c_247,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_203])).

tff(c_8209,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8202,c_247])).

tff(c_248,plain,(
    ! [C_71,B_72,A_73] :
      ( v5_relat_1(C_71,B_72)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_73,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_266,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_84,c_248])).

tff(c_8313,plain,(
    ! [B_547,A_548] :
      ( k2_relat_1(B_547) = A_548
      | ~ v2_funct_2(B_547,A_548)
      | ~ v5_relat_1(B_547,A_548)
      | ~ v1_relat_1(B_547) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_8322,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_266,c_8313])).

tff(c_8334,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_8322])).

tff(c_8335,plain,(
    ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_8209,c_8334])).

tff(c_8531,plain,(
    ! [C_578,B_579,A_580] :
      ( v2_funct_2(C_578,B_579)
      | ~ v3_funct_2(C_578,A_580,B_579)
      | ~ v1_funct_1(C_578)
      | ~ m1_subset_1(C_578,k1_zfmisc_1(k2_zfmisc_1(A_580,B_579))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_8544,plain,
    ( v2_funct_2('#skF_3','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_8531])).

tff(c_8553,plain,(
    v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_86,c_8544])).

tff(c_8555,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8335,c_8553])).

tff(c_8556,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_203])).

tff(c_2,plain,(
    ! [A_1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8566,plain,(
    ! [A_1] : m1_subset_1('#skF_3',k1_zfmisc_1(A_1)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8556,c_2])).

tff(c_9551,plain,(
    ! [A_699,B_700,C_701,D_702] :
      ( r2_relset_1(A_699,B_700,C_701,C_701)
      | ~ m1_subset_1(D_702,k1_zfmisc_1(k2_zfmisc_1(A_699,B_700)))
      | ~ m1_subset_1(C_701,k1_zfmisc_1(k2_zfmisc_1(A_699,B_700))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_10601,plain,(
    ! [A_805,B_806,C_807] :
      ( r2_relset_1(A_805,B_806,C_807,C_807)
      | ~ m1_subset_1(C_807,k1_zfmisc_1(k2_zfmisc_1(A_805,B_806))) ) ),
    inference(resolution,[status(thm)],[c_8566,c_9551])).

tff(c_10615,plain,(
    ! [A_805,B_806] : r2_relset_1(A_805,B_806,'#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_8566,c_10601])).

tff(c_9266,plain,(
    ! [C_677,A_678,B_679] :
      ( v2_funct_1(C_677)
      | ~ v3_funct_2(C_677,A_678,B_679)
      | ~ v1_funct_1(C_677)
      | ~ m1_subset_1(C_677,k1_zfmisc_1(k2_zfmisc_1(A_678,B_679))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_9270,plain,(
    ! [A_678,B_679] :
      ( v2_funct_1('#skF_3')
      | ~ v3_funct_2('#skF_3',A_678,B_679)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_8566,c_9266])).

tff(c_9279,plain,(
    ! [A_678,B_679] :
      ( v2_funct_1('#skF_3')
      | ~ v3_funct_2('#skF_3',A_678,B_679) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_9270])).

tff(c_9285,plain,(
    ! [A_678,B_679] : ~ v3_funct_2('#skF_3',A_678,B_679) ),
    inference(splitLeft,[status(thm)],[c_9279])).

tff(c_8595,plain,(
    ! [A_583] :
      ( A_583 != '#skF_3'
      | k6_partfun1(A_583) = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8556,c_8556,c_214])).

tff(c_8601,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),'#skF_3')
    | '#skF_2' != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_8595,c_140])).

tff(c_8660,plain,(
    '#skF_2' != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_8601])).

tff(c_8883,plain,(
    ! [C_629,B_630,A_631] :
      ( v2_funct_2(C_629,B_630)
      | ~ v3_funct_2(C_629,A_631,B_630)
      | ~ v1_funct_1(C_629)
      | ~ m1_subset_1(C_629,k1_zfmisc_1(k2_zfmisc_1(A_631,B_630))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_8887,plain,(
    ! [B_630,A_631] :
      ( v2_funct_2('#skF_3',B_630)
      | ~ v3_funct_2('#skF_3',A_631,B_630)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_8566,c_8883])).

tff(c_9048,plain,(
    ! [B_643,A_644] :
      ( v2_funct_2('#skF_3',B_643)
      | ~ v3_funct_2('#skF_3',A_644,B_643) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_8887])).

tff(c_9056,plain,(
    v2_funct_2('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_86,c_9048])).

tff(c_8557,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_203])).

tff(c_8572,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8556,c_8557])).

tff(c_8638,plain,(
    ! [C_586,B_587,A_588] :
      ( v5_relat_1(C_586,B_587)
      | ~ m1_subset_1(C_586,k1_zfmisc_1(k2_zfmisc_1(A_588,B_587))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8649,plain,(
    ! [B_587] : v5_relat_1('#skF_3',B_587) ),
    inference(resolution,[status(thm)],[c_8566,c_8638])).

tff(c_8736,plain,(
    ! [B_604,A_605] :
      ( k2_relat_1(B_604) = A_605
      | ~ v2_funct_2(B_604,A_605)
      | ~ v5_relat_1(B_604,A_605)
      | ~ v1_relat_1(B_604) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_8742,plain,(
    ! [B_587] :
      ( k2_relat_1('#skF_3') = B_587
      | ~ v2_funct_2('#skF_3',B_587)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_8649,c_8736])).

tff(c_8751,plain,(
    ! [B_587] :
      ( B_587 = '#skF_3'
      | ~ v2_funct_2('#skF_3',B_587) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_8572,c_8742])).

tff(c_9059,plain,(
    '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_9056,c_8751])).

tff(c_9063,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8660,c_9059])).

tff(c_9065,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_8601])).

tff(c_9067,plain,(
    v3_funct_2('#skF_3','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9065,c_9065,c_86])).

tff(c_9287,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9285,c_9067])).

tff(c_9288,plain,(
    v2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_9279])).

tff(c_8594,plain,(
    k6_partfun1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8556,c_8556,c_214])).

tff(c_218,plain,(
    ! [A_70] :
      ( k1_xboole_0 != A_70
      | k6_partfun1(A_70) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_210])).

tff(c_10,plain,(
    ! [A_6] : k1_relat_1(k6_relat_1(A_6)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_94,plain,(
    ! [A_6] : k1_relat_1(k6_partfun1(A_6)) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_10])).

tff(c_232,plain,(
    ! [A_70] :
      ( k1_relat_1(k1_xboole_0) = A_70
      | k1_xboole_0 != A_70 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_94])).

tff(c_8629,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8556,c_8556,c_232])).

tff(c_66,plain,(
    ! [A_32] : v1_funct_1('#skF_1'(A_32)) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_62,plain,(
    ! [A_32] : v3_funct_2('#skF_1'(A_32),A_32,A_32) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_9411,plain,(
    ! [C_688,B_689,A_690] :
      ( v2_funct_2(C_688,B_689)
      | ~ v3_funct_2(C_688,A_690,B_689)
      | ~ v1_funct_1(C_688)
      | ~ m1_subset_1(C_688,k1_zfmisc_1(k2_zfmisc_1(A_690,B_689))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_9421,plain,(
    ! [A_32] :
      ( v2_funct_2('#skF_1'(A_32),A_32)
      | ~ v3_funct_2('#skF_1'(A_32),A_32,A_32)
      | ~ v1_funct_1('#skF_1'(A_32)) ) ),
    inference(resolution,[status(thm)],[c_74,c_9411])).

tff(c_9429,plain,(
    ! [A_32] : v2_funct_2('#skF_1'(A_32),A_32) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_9421])).

tff(c_72,plain,(
    ! [A_32] : v1_relat_1('#skF_1'(A_32)) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_68,plain,(
    ! [A_32] : v5_relat_1('#skF_1'(A_32),A_32) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_9145,plain,(
    ! [B_660,A_661] :
      ( k2_relat_1(B_660) = A_661
      | ~ v2_funct_2(B_660,A_661)
      | ~ v5_relat_1(B_660,A_661)
      | ~ v1_relat_1(B_660) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_9154,plain,(
    ! [A_32] :
      ( k2_relat_1('#skF_1'(A_32)) = A_32
      | ~ v2_funct_2('#skF_1'(A_32),A_32)
      | ~ v1_relat_1('#skF_1'(A_32)) ) ),
    inference(resolution,[status(thm)],[c_68,c_9145])).

tff(c_9163,plain,(
    ! [A_32] :
      ( k2_relat_1('#skF_1'(A_32)) = A_32
      | ~ v2_funct_2('#skF_1'(A_32),A_32) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_9154])).

tff(c_9431,plain,(
    ! [A_32] : k2_relat_1('#skF_1'(A_32)) = A_32 ),
    inference(demodulation,[status(thm),theory(equality)],[c_9429,c_9163])).

tff(c_133,plain,(
    ! [A_55] :
      ( k2_relat_1(A_55) != k1_xboole_0
      | k1_xboole_0 = A_55
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_137,plain,(
    ! [A_32] :
      ( k2_relat_1('#skF_1'(A_32)) != k1_xboole_0
      | '#skF_1'(A_32) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_72,c_133])).

tff(c_8562,plain,(
    ! [A_32] :
      ( k2_relat_1('#skF_1'(A_32)) != '#skF_3'
      | '#skF_1'(A_32) = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8556,c_8556,c_137])).

tff(c_9437,plain,(
    ! [A_32] :
      ( A_32 != '#skF_3'
      | '#skF_1'(A_32) = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9431,c_8562])).

tff(c_64,plain,(
    ! [A_32] : v1_funct_2('#skF_1'(A_32),A_32,A_32) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_9695,plain,(
    ! [A_725,B_726] :
      ( k2_funct_2(A_725,B_726) = k2_funct_1(B_726)
      | ~ m1_subset_1(B_726,k1_zfmisc_1(k2_zfmisc_1(A_725,A_725)))
      | ~ v3_funct_2(B_726,A_725,A_725)
      | ~ v1_funct_2(B_726,A_725,A_725)
      | ~ v1_funct_1(B_726) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_9705,plain,(
    ! [A_32] :
      ( k2_funct_2(A_32,'#skF_1'(A_32)) = k2_funct_1('#skF_1'(A_32))
      | ~ v3_funct_2('#skF_1'(A_32),A_32,A_32)
      | ~ v1_funct_2('#skF_1'(A_32),A_32,A_32)
      | ~ v1_funct_1('#skF_1'(A_32)) ) ),
    inference(resolution,[status(thm)],[c_74,c_9695])).

tff(c_9712,plain,(
    ! [A_32] : k2_funct_2(A_32,'#skF_1'(A_32)) = k2_funct_1('#skF_1'(A_32)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_9705])).

tff(c_9868,plain,(
    ! [A_746,B_747] :
      ( m1_subset_1(k2_funct_2(A_746,B_747),k1_zfmisc_1(k2_zfmisc_1(A_746,A_746)))
      | ~ m1_subset_1(B_747,k1_zfmisc_1(k2_zfmisc_1(A_746,A_746)))
      | ~ v3_funct_2(B_747,A_746,A_746)
      | ~ v1_funct_2(B_747,A_746,A_746)
      | ~ v1_funct_1(B_747) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_9923,plain,(
    ! [A_32] :
      ( m1_subset_1(k2_funct_1('#skF_1'(A_32)),k1_zfmisc_1(k2_zfmisc_1(A_32,A_32)))
      | ~ m1_subset_1('#skF_1'(A_32),k1_zfmisc_1(k2_zfmisc_1(A_32,A_32)))
      | ~ v3_funct_2('#skF_1'(A_32),A_32,A_32)
      | ~ v1_funct_2('#skF_1'(A_32),A_32,A_32)
      | ~ v1_funct_1('#skF_1'(A_32)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9712,c_9868])).

tff(c_9945,plain,(
    ! [A_748] : m1_subset_1(k2_funct_1('#skF_1'(A_748)),k1_zfmisc_1(k2_zfmisc_1(A_748,A_748))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_74,c_9923])).

tff(c_18,plain,(
    ! [C_10,A_8,B_9] :
      ( v1_relat_1(C_10)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_10048,plain,(
    ! [A_750] : v1_relat_1(k2_funct_1('#skF_1'(A_750))) ),
    inference(resolution,[status(thm)],[c_9945,c_18])).

tff(c_10058,plain,(
    ! [A_32] :
      ( v1_relat_1(k2_funct_1('#skF_3'))
      | A_32 != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9437,c_10048])).

tff(c_10111,plain,(
    ! [A_32] : A_32 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_10058])).

tff(c_9179,plain,(
    ! [A_666,B_667,C_668] :
      ( k1_relset_1(A_666,B_667,C_668) = k1_relat_1(C_668)
      | ~ m1_subset_1(C_668,k1_zfmisc_1(k2_zfmisc_1(A_666,B_667))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_9183,plain,(
    ! [A_666,B_667] : k1_relset_1(A_666,B_667,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8566,c_9179])).

tff(c_9191,plain,(
    ! [A_666,B_667] : k1_relset_1(A_666,B_667,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8629,c_9183])).

tff(c_10132,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10111,c_9191])).

tff(c_10133,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_10058])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_relat_1(A_5) != k1_xboole_0
      | k1_xboole_0 = A_5
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8563,plain,(
    ! [A_5] :
      ( k1_relat_1(A_5) != '#skF_3'
      | A_5 = '#skF_3'
      | ~ v1_relat_1(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8556,c_8556,c_8])).

tff(c_10141,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) != '#skF_3'
    | k2_funct_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_10133,c_8563])).

tff(c_10242,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_10141])).

tff(c_9834,plain,(
    ! [A_739,B_740] :
      ( v1_funct_2(k2_funct_2(A_739,B_740),A_739,A_739)
      | ~ m1_subset_1(B_740,k1_zfmisc_1(k2_zfmisc_1(A_739,A_739)))
      | ~ v3_funct_2(B_740,A_739,A_739)
      | ~ v1_funct_2(B_740,A_739,A_739)
      | ~ v1_funct_1(B_740) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_9841,plain,(
    ! [A_32] :
      ( v1_funct_2(k2_funct_2(A_32,'#skF_1'(A_32)),A_32,A_32)
      | ~ v3_funct_2('#skF_1'(A_32),A_32,A_32)
      | ~ v1_funct_2('#skF_1'(A_32),A_32,A_32)
      | ~ v1_funct_1('#skF_1'(A_32)) ) ),
    inference(resolution,[status(thm)],[c_74,c_9834])).

tff(c_9849,plain,(
    ! [A_741] : v1_funct_2(k2_funct_1('#skF_1'(A_741)),A_741,A_741) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_9712,c_9841])).

tff(c_9856,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_9437,c_9849])).

tff(c_10404,plain,(
    ! [A_797] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(A_797,A_797)))
      | A_797 != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9437,c_9945])).

tff(c_42,plain,(
    ! [B_25,C_26] :
      ( k1_relset_1(k1_xboole_0,B_25,C_26) = k1_xboole_0
      | ~ v1_funct_2(C_26,k1_xboole_0,B_25)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_9289,plain,(
    ! [B_25,C_26] :
      ( k1_relset_1('#skF_3',B_25,C_26) = '#skF_3'
      | ~ v1_funct_2(C_26,'#skF_3',B_25)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_25))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8556,c_8556,c_8556,c_8556,c_42])).

tff(c_10437,plain,
    ( k1_relset_1('#skF_3','#skF_3',k2_funct_1('#skF_3')) = '#skF_3'
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_10404,c_9289])).

tff(c_10487,plain,(
    k1_relset_1('#skF_3','#skF_3',k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9856,c_10437])).

tff(c_24,plain,(
    ! [A_14,B_15,C_16] :
      ( k1_relset_1(A_14,B_15,C_16) = k1_relat_1(C_16)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_10495,plain,(
    ! [A_797] :
      ( k1_relset_1(A_797,A_797,k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3'))
      | A_797 != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_10404,c_24])).

tff(c_10514,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_10487,c_10495])).

tff(c_10523,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10242,c_10514])).

tff(c_10524,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_10141])).

tff(c_10543,plain,
    ( k6_partfun1(k1_relat_1('#skF_3')) = k5_relat_1('#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10524,c_91])).

tff(c_10550,plain,(
    k5_relat_1('#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_90,c_9288,c_8594,c_8629,c_10543])).

tff(c_10061,plain,(
    ! [C_756,F_753,E_754,A_751,D_752,B_755] :
      ( k1_partfun1(A_751,B_755,C_756,D_752,E_754,F_753) = k5_relat_1(E_754,F_753)
      | ~ m1_subset_1(F_753,k1_zfmisc_1(k2_zfmisc_1(C_756,D_752)))
      | ~ v1_funct_1(F_753)
      | ~ m1_subset_1(E_754,k1_zfmisc_1(k2_zfmisc_1(A_751,B_755)))
      | ~ v1_funct_1(E_754) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_10072,plain,(
    ! [A_751,B_755,A_32,E_754] :
      ( k1_partfun1(A_751,B_755,A_32,A_32,E_754,'#skF_1'(A_32)) = k5_relat_1(E_754,'#skF_1'(A_32))
      | ~ v1_funct_1('#skF_1'(A_32))
      | ~ m1_subset_1(E_754,k1_zfmisc_1(k2_zfmisc_1(A_751,B_755)))
      | ~ v1_funct_1(E_754) ) ),
    inference(resolution,[status(thm)],[c_74,c_10061])).

tff(c_10560,plain,(
    ! [A_799,B_800,A_801,E_802] :
      ( k1_partfun1(A_799,B_800,A_801,A_801,E_802,'#skF_1'(A_801)) = k5_relat_1(E_802,'#skF_1'(A_801))
      | ~ m1_subset_1(E_802,k1_zfmisc_1(k2_zfmisc_1(A_799,B_800)))
      | ~ v1_funct_1(E_802) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_10072])).

tff(c_10567,plain,(
    ! [A_799,B_800,A_801] :
      ( k1_partfun1(A_799,B_800,A_801,A_801,'#skF_3','#skF_1'(A_801)) = k5_relat_1('#skF_3','#skF_1'(A_801))
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_8566,c_10560])).

tff(c_16050,plain,(
    ! [A_1051,B_1052,A_1053] : k1_partfun1(A_1051,B_1052,A_1053,A_1053,'#skF_3','#skF_1'(A_1053)) = k5_relat_1('#skF_3','#skF_1'(A_1053)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_10567])).

tff(c_19258,plain,(
    ! [A_1146,A_1147,B_1148] :
      ( k5_relat_1('#skF_3','#skF_1'(A_1146)) = k1_partfun1(A_1147,B_1148,A_1146,A_1146,'#skF_3','#skF_3')
      | A_1146 != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9437,c_16050])).

tff(c_19279,plain,(
    ! [A_1147,B_1148,A_32] :
      ( k1_partfun1(A_1147,B_1148,A_32,A_32,'#skF_3','#skF_3') = k5_relat_1('#skF_3','#skF_3')
      | A_32 != '#skF_3'
      | A_32 != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9437,c_19258])).

tff(c_19313,plain,(
    ! [A_1150,B_1151,A_1152] :
      ( k1_partfun1(A_1150,B_1151,A_1152,A_1152,'#skF_3','#skF_3') = '#skF_3'
      | A_1152 != '#skF_3'
      | A_1152 != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10550,c_19279])).

tff(c_9714,plain,(
    ! [A_727] : k2_funct_2(A_727,'#skF_1'(A_727)) = k2_funct_1('#skF_1'(A_727)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_9705])).

tff(c_9723,plain,(
    ! [A_32] :
      ( k2_funct_1('#skF_1'(A_32)) = k2_funct_2(A_32,'#skF_3')
      | A_32 != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9437,c_9714])).

tff(c_11031,plain,(
    ! [A_842] :
      ( k1_relat_1(k2_funct_1('#skF_1'(A_842))) != '#skF_3'
      | k2_funct_1('#skF_1'(A_842)) = '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_10048,c_8563])).

tff(c_11040,plain,(
    ! [A_32] :
      ( k1_relat_1(k2_funct_1('#skF_3')) != '#skF_3'
      | k2_funct_1('#skF_1'(A_32)) = '#skF_3'
      | A_32 != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9437,c_11031])).

tff(c_11044,plain,(
    ! [A_843] :
      ( k2_funct_1('#skF_1'(A_843)) = '#skF_3'
      | A_843 != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8629,c_10524,c_11040])).

tff(c_11219,plain,(
    ! [A_846] :
      ( k2_funct_2(A_846,'#skF_3') = '#skF_3'
      | A_846 != '#skF_3'
      | A_846 != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9723,c_11044])).

tff(c_9066,plain,(
    ~ r2_relset_1('#skF_3','#skF_3',k1_partfun1('#skF_3','#skF_3','#skF_3','#skF_3','#skF_3',k2_funct_2('#skF_3','#skF_3')),k6_partfun1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9065,c_9065,c_9065,c_9065,c_9065,c_9065,c_9065,c_9065,c_140])).

tff(c_9069,plain,(
    ~ r2_relset_1('#skF_3','#skF_3',k1_partfun1('#skF_3','#skF_3','#skF_3','#skF_3','#skF_3',k2_funct_2('#skF_3','#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8594,c_9066])).

tff(c_11308,plain,(
    ~ r2_relset_1('#skF_3','#skF_3',k1_partfun1('#skF_3','#skF_3','#skF_3','#skF_3','#skF_3','#skF_3'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_11219,c_9069])).

tff(c_19322,plain,(
    ~ r2_relset_1('#skF_3','#skF_3','#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_19313,c_11308])).

tff(c_19333,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10615,c_19322])).

tff(c_19334,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_20572,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20569,c_19334])).

tff(c_21408,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k5_relat_1(k2_funct_1('#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21347,c_20572])).

tff(c_21444,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1(k2_relat_1('#skF_3')),k6_partfun1('#skF_2'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_21408])).

tff(c_21450,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_19361,c_90,c_19837,c_20701,c_19709,c_21444])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:11:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.16/5.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.16/5.68  
% 14.16/5.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.16/5.69  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 14.16/5.69  
% 14.16/5.69  %Foreground sorts:
% 14.16/5.69  
% 14.16/5.69  
% 14.16/5.69  %Background operators:
% 14.16/5.69  
% 14.16/5.69  
% 14.16/5.69  %Foreground operators:
% 14.16/5.69  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 14.16/5.69  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 14.16/5.69  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 14.16/5.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.16/5.69  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 14.16/5.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.16/5.69  tff('#skF_1', type, '#skF_1': $i > $i).
% 14.16/5.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.16/5.69  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 14.16/5.69  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 14.16/5.69  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 14.16/5.69  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 14.16/5.69  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 14.16/5.69  tff('#skF_2', type, '#skF_2': $i).
% 14.16/5.69  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 14.16/5.69  tff('#skF_3', type, '#skF_3': $i).
% 14.16/5.69  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 14.16/5.69  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 14.16/5.69  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 14.16/5.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.16/5.69  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 14.16/5.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.16/5.69  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 14.16/5.69  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 14.16/5.69  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 14.16/5.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.16/5.69  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 14.16/5.69  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 14.16/5.69  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 14.16/5.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.16/5.69  
% 14.43/5.72  tff(f_183, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_funct_2)).
% 14.43/5.72  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 14.43/5.72  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 14.43/5.72  tff(f_133, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 14.43/5.72  tff(f_148, axiom, (![A]: (?[B]: ((((((m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) & v1_relat_1(B)) & v4_relat_1(B, A)) & v5_relat_1(B, A)) & v1_funct_1(B)) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc2_funct_2)).
% 14.43/5.72  tff(f_75, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 14.43/5.72  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 14.43/5.72  tff(f_113, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 14.43/5.72  tff(f_170, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 14.43/5.72  tff(f_55, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 14.43/5.72  tff(f_168, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 14.43/5.72  tff(f_129, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 14.43/5.72  tff(f_158, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 14.43/5.72  tff(f_45, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 14.43/5.72  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 14.43/5.72  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 14.43/5.72  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 14.43/5.72  tff(f_27, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 14.43/5.72  tff(c_84, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_183])).
% 14.43/5.72  tff(c_19343, plain, (![C_1156, A_1157, B_1158]: (v1_relat_1(C_1156) | ~m1_subset_1(C_1156, k1_zfmisc_1(k2_zfmisc_1(A_1157, B_1158))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 14.43/5.72  tff(c_19361, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_19343])).
% 14.43/5.72  tff(c_90, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_183])).
% 14.43/5.72  tff(c_86, plain, (v3_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_183])).
% 14.43/5.72  tff(c_19816, plain, (![C_1223, A_1224, B_1225]: (v2_funct_1(C_1223) | ~v3_funct_2(C_1223, A_1224, B_1225) | ~v1_funct_1(C_1223) | ~m1_subset_1(C_1223, k1_zfmisc_1(k2_zfmisc_1(A_1224, B_1225))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 14.43/5.72  tff(c_19829, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_19816])).
% 14.43/5.72  tff(c_19837, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_86, c_19829])).
% 14.43/5.72  tff(c_60, plain, (![A_31]: (m1_subset_1(k6_partfun1(A_31), k1_zfmisc_1(k2_zfmisc_1(A_31, A_31))))), inference(cnfTransformation, [status(thm)], [f_133])).
% 14.43/5.72  tff(c_74, plain, (![A_32]: (m1_subset_1('#skF_1'(A_32), k1_zfmisc_1(k2_zfmisc_1(A_32, A_32))))), inference(cnfTransformation, [status(thm)], [f_148])).
% 14.43/5.72  tff(c_20275, plain, (![A_1260, B_1261, C_1262, D_1263]: (r2_relset_1(A_1260, B_1261, C_1262, C_1262) | ~m1_subset_1(D_1263, k1_zfmisc_1(k2_zfmisc_1(A_1260, B_1261))) | ~m1_subset_1(C_1262, k1_zfmisc_1(k2_zfmisc_1(A_1260, B_1261))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 14.43/5.72  tff(c_20691, plain, (![A_1297, C_1298]: (r2_relset_1(A_1297, A_1297, C_1298, C_1298) | ~m1_subset_1(C_1298, k1_zfmisc_1(k2_zfmisc_1(A_1297, A_1297))))), inference(resolution, [status(thm)], [c_74, c_20275])).
% 14.43/5.72  tff(c_20701, plain, (![A_31]: (r2_relset_1(A_31, A_31, k6_partfun1(A_31), k6_partfun1(A_31)))), inference(resolution, [status(thm)], [c_60, c_20691])).
% 14.43/5.72  tff(c_19391, plain, (![C_1160, B_1161, A_1162]: (v5_relat_1(C_1160, B_1161) | ~m1_subset_1(C_1160, k1_zfmisc_1(k2_zfmisc_1(A_1162, B_1161))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 14.43/5.72  tff(c_19409, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_84, c_19391])).
% 14.43/5.72  tff(c_19529, plain, (![B_1187, A_1188]: (k2_relat_1(B_1187)=A_1188 | ~v2_funct_2(B_1187, A_1188) | ~v5_relat_1(B_1187, A_1188) | ~v1_relat_1(B_1187))), inference(cnfTransformation, [status(thm)], [f_113])).
% 14.43/5.72  tff(c_19535, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_19409, c_19529])).
% 14.43/5.72  tff(c_19547, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_19361, c_19535])).
% 14.43/5.72  tff(c_19559, plain, (~v2_funct_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_19547])).
% 14.43/5.72  tff(c_19684, plain, (![C_1208, B_1209, A_1210]: (v2_funct_2(C_1208, B_1209) | ~v3_funct_2(C_1208, A_1210, B_1209) | ~v1_funct_1(C_1208) | ~m1_subset_1(C_1208, k1_zfmisc_1(k2_zfmisc_1(A_1210, B_1209))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 14.43/5.72  tff(c_19697, plain, (v2_funct_2('#skF_3', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_19684])).
% 14.43/5.72  tff(c_19706, plain, (v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_86, c_19697])).
% 14.43/5.72  tff(c_19708, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19559, c_19706])).
% 14.43/5.72  tff(c_19709, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_19547])).
% 14.43/5.72  tff(c_80, plain, (![A_42]: (k6_relat_1(A_42)=k6_partfun1(A_42))), inference(cnfTransformation, [status(thm)], [f_170])).
% 14.43/5.72  tff(c_14, plain, (![A_7]: (k5_relat_1(k2_funct_1(A_7), A_7)=k6_relat_1(k2_relat_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_55])).
% 14.43/5.72  tff(c_92, plain, (![A_7]: (k5_relat_1(k2_funct_1(A_7), A_7)=k6_partfun1(k2_relat_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_14])).
% 14.43/5.72  tff(c_88, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_183])).
% 14.43/5.72  tff(c_20546, plain, (![A_1288, B_1289]: (k2_funct_2(A_1288, B_1289)=k2_funct_1(B_1289) | ~m1_subset_1(B_1289, k1_zfmisc_1(k2_zfmisc_1(A_1288, A_1288))) | ~v3_funct_2(B_1289, A_1288, A_1288) | ~v1_funct_2(B_1289, A_1288, A_1288) | ~v1_funct_1(B_1289))), inference(cnfTransformation, [status(thm)], [f_168])).
% 14.43/5.72  tff(c_20559, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_20546])).
% 14.43/5.72  tff(c_20569, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_20559])).
% 14.43/5.72  tff(c_20516, plain, (![A_1284, B_1285]: (v1_funct_1(k2_funct_2(A_1284, B_1285)) | ~m1_subset_1(B_1285, k1_zfmisc_1(k2_zfmisc_1(A_1284, A_1284))) | ~v3_funct_2(B_1285, A_1284, A_1284) | ~v1_funct_2(B_1285, A_1284, A_1284) | ~v1_funct_1(B_1285))), inference(cnfTransformation, [status(thm)], [f_129])).
% 14.43/5.72  tff(c_20529, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_20516])).
% 14.43/5.72  tff(c_20539, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_20529])).
% 14.43/5.72  tff(c_20570, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_20569, c_20539])).
% 14.43/5.72  tff(c_50, plain, (![A_29, B_30]: (m1_subset_1(k2_funct_2(A_29, B_30), k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))) | ~m1_subset_1(B_30, k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))) | ~v3_funct_2(B_30, A_29, A_29) | ~v1_funct_2(B_30, A_29, A_29) | ~v1_funct_1(B_30))), inference(cnfTransformation, [status(thm)], [f_129])).
% 14.43/5.72  tff(c_20975, plain, (![A_1316, E_1319, F_1318, C_1321, B_1320, D_1317]: (k1_partfun1(A_1316, B_1320, C_1321, D_1317, E_1319, F_1318)=k5_relat_1(E_1319, F_1318) | ~m1_subset_1(F_1318, k1_zfmisc_1(k2_zfmisc_1(C_1321, D_1317))) | ~v1_funct_1(F_1318) | ~m1_subset_1(E_1319, k1_zfmisc_1(k2_zfmisc_1(A_1316, B_1320))) | ~v1_funct_1(E_1319))), inference(cnfTransformation, [status(thm)], [f_158])).
% 14.43/5.72  tff(c_20988, plain, (![A_1316, B_1320, E_1319]: (k1_partfun1(A_1316, B_1320, '#skF_2', '#skF_2', E_1319, '#skF_3')=k5_relat_1(E_1319, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_1319, k1_zfmisc_1(k2_zfmisc_1(A_1316, B_1320))) | ~v1_funct_1(E_1319))), inference(resolution, [status(thm)], [c_84, c_20975])).
% 14.43/5.72  tff(c_21018, plain, (![A_1322, B_1323, E_1324]: (k1_partfun1(A_1322, B_1323, '#skF_2', '#skF_2', E_1324, '#skF_3')=k5_relat_1(E_1324, '#skF_3') | ~m1_subset_1(E_1324, k1_zfmisc_1(k2_zfmisc_1(A_1322, B_1323))) | ~v1_funct_1(E_1324))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_20988])).
% 14.43/5.72  tff(c_21315, plain, (![A_1339, B_1340]: (k1_partfun1(A_1339, A_1339, '#skF_2', '#skF_2', k2_funct_2(A_1339, B_1340), '#skF_3')=k5_relat_1(k2_funct_2(A_1339, B_1340), '#skF_3') | ~v1_funct_1(k2_funct_2(A_1339, B_1340)) | ~m1_subset_1(B_1340, k1_zfmisc_1(k2_zfmisc_1(A_1339, A_1339))) | ~v3_funct_2(B_1340, A_1339, A_1339) | ~v1_funct_2(B_1340, A_1339, A_1339) | ~v1_funct_1(B_1340))), inference(resolution, [status(thm)], [c_50, c_21018])).
% 14.43/5.72  tff(c_21330, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3')=k5_relat_1(k2_funct_2('#skF_2', '#skF_3'), '#skF_3') | ~v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_21315])).
% 14.43/5.72  tff(c_21347, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_20570, c_20569, c_20569, c_20569, c_21330])).
% 14.43/5.72  tff(c_148, plain, (![C_61, A_62, B_63]: (v1_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 14.43/5.72  tff(c_166, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_148])).
% 14.43/5.72  tff(c_782, plain, (![C_133, A_134, B_135]: (v2_funct_1(C_133) | ~v3_funct_2(C_133, A_134, B_135) | ~v1_funct_1(C_133) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 14.43/5.72  tff(c_795, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_782])).
% 14.43/5.72  tff(c_803, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_86, c_795])).
% 14.43/5.72  tff(c_1245, plain, (![A_169, B_170, C_171, D_172]: (r2_relset_1(A_169, B_170, C_171, C_171) | ~m1_subset_1(D_172, k1_zfmisc_1(k2_zfmisc_1(A_169, B_170))) | ~m1_subset_1(C_171, k1_zfmisc_1(k2_zfmisc_1(A_169, B_170))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 14.43/5.72  tff(c_1258, plain, (![A_173, C_174]: (r2_relset_1(A_173, A_173, C_174, C_174) | ~m1_subset_1(C_174, k1_zfmisc_1(k2_zfmisc_1(A_173, A_173))))), inference(resolution, [status(thm)], [c_60, c_1245])).
% 14.43/5.72  tff(c_1268, plain, (![A_31]: (r2_relset_1(A_31, A_31, k6_partfun1(A_31), k6_partfun1(A_31)))), inference(resolution, [status(thm)], [c_60, c_1258])).
% 14.43/5.72  tff(c_12, plain, (![A_6]: (k2_relat_1(k6_relat_1(A_6))=A_6)), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.43/5.72  tff(c_93, plain, (![A_6]: (k2_relat_1(k6_partfun1(A_6))=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_80, c_12])).
% 14.43/5.72  tff(c_204, plain, (![A_67]: (v1_relat_1(k6_partfun1(A_67)))), inference(resolution, [status(thm)], [c_60, c_148])).
% 14.43/5.72  tff(c_6, plain, (![A_5]: (k2_relat_1(A_5)!=k1_xboole_0 | k1_xboole_0=A_5 | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 14.43/5.72  tff(c_210, plain, (![A_67]: (k2_relat_1(k6_partfun1(A_67))!=k1_xboole_0 | k6_partfun1(A_67)=k1_xboole_0)), inference(resolution, [status(thm)], [c_204, c_6])).
% 14.43/5.72  tff(c_214, plain, (![A_67]: (k1_xboole_0!=A_67 | k6_partfun1(A_67)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_93, c_210])).
% 14.43/5.72  tff(c_82, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2')) | ~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_183])).
% 14.43/5.72  tff(c_140, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(splitLeft, [status(thm)], [c_82])).
% 14.43/5.72  tff(c_275, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k1_xboole_0) | k1_xboole_0!='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_214, c_140])).
% 14.43/5.72  tff(c_311, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_275])).
% 14.43/5.72  tff(c_687, plain, (![A_119, B_120, C_121]: (k1_relset_1(A_119, B_120, C_121)=k1_relat_1(C_121) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 14.43/5.72  tff(c_706, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_687])).
% 14.43/5.72  tff(c_1128, plain, (![B_154, A_155, C_156]: (k1_xboole_0=B_154 | k1_relset_1(A_155, B_154, C_156)=A_155 | ~v1_funct_2(C_156, A_155, B_154) | ~m1_subset_1(C_156, k1_zfmisc_1(k2_zfmisc_1(A_155, B_154))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 14.43/5.72  tff(c_1141, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_2', '#skF_2', '#skF_3')='#skF_2' | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_84, c_1128])).
% 14.43/5.72  tff(c_1151, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_706, c_1141])).
% 14.43/5.72  tff(c_1152, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_311, c_1151])).
% 14.43/5.72  tff(c_16, plain, (![A_7]: (k5_relat_1(A_7, k2_funct_1(A_7))=k6_relat_1(k1_relat_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_55])).
% 14.43/5.72  tff(c_91, plain, (![A_7]: (k5_relat_1(A_7, k2_funct_1(A_7))=k6_partfun1(k1_relat_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_16])).
% 14.43/5.72  tff(c_1335, plain, (![A_185, B_186]: (k2_funct_2(A_185, B_186)=k2_funct_1(B_186) | ~m1_subset_1(B_186, k1_zfmisc_1(k2_zfmisc_1(A_185, A_185))) | ~v3_funct_2(B_186, A_185, A_185) | ~v1_funct_2(B_186, A_185, A_185) | ~v1_funct_1(B_186))), inference(cnfTransformation, [status(thm)], [f_168])).
% 14.43/5.72  tff(c_1348, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_1335])).
% 14.43/5.72  tff(c_1358, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_1348])).
% 14.43/5.72  tff(c_1305, plain, (![A_181, B_182]: (v1_funct_1(k2_funct_2(A_181, B_182)) | ~m1_subset_1(B_182, k1_zfmisc_1(k2_zfmisc_1(A_181, A_181))) | ~v3_funct_2(B_182, A_181, A_181) | ~v1_funct_2(B_182, A_181, A_181) | ~v1_funct_1(B_182))), inference(cnfTransformation, [status(thm)], [f_129])).
% 14.43/5.72  tff(c_1318, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_1305])).
% 14.43/5.72  tff(c_1328, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_1318])).
% 14.43/5.72  tff(c_1359, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1358, c_1328])).
% 14.43/5.72  tff(c_1743, plain, (![F_214, C_217, B_216, D_213, A_212, E_215]: (k1_partfun1(A_212, B_216, C_217, D_213, E_215, F_214)=k5_relat_1(E_215, F_214) | ~m1_subset_1(F_214, k1_zfmisc_1(k2_zfmisc_1(C_217, D_213))) | ~v1_funct_1(F_214) | ~m1_subset_1(E_215, k1_zfmisc_1(k2_zfmisc_1(A_212, B_216))) | ~v1_funct_1(E_215))), inference(cnfTransformation, [status(thm)], [f_158])).
% 14.43/5.72  tff(c_7869, plain, (![E_521, B_519, A_518, A_520, B_517]: (k1_partfun1(A_518, B_517, A_520, A_520, E_521, k2_funct_2(A_520, B_519))=k5_relat_1(E_521, k2_funct_2(A_520, B_519)) | ~v1_funct_1(k2_funct_2(A_520, B_519)) | ~m1_subset_1(E_521, k1_zfmisc_1(k2_zfmisc_1(A_518, B_517))) | ~v1_funct_1(E_521) | ~m1_subset_1(B_519, k1_zfmisc_1(k2_zfmisc_1(A_520, A_520))) | ~v3_funct_2(B_519, A_520, A_520) | ~v1_funct_2(B_519, A_520, A_520) | ~v1_funct_1(B_519))), inference(resolution, [status(thm)], [c_50, c_1743])).
% 14.43/5.72  tff(c_7892, plain, (![A_520, B_519]: (k1_partfun1('#skF_2', '#skF_2', A_520, A_520, '#skF_3', k2_funct_2(A_520, B_519))=k5_relat_1('#skF_3', k2_funct_2(A_520, B_519)) | ~v1_funct_1(k2_funct_2(A_520, B_519)) | ~v1_funct_1('#skF_3') | ~m1_subset_1(B_519, k1_zfmisc_1(k2_zfmisc_1(A_520, A_520))) | ~v3_funct_2(B_519, A_520, A_520) | ~v1_funct_2(B_519, A_520, A_520) | ~v1_funct_1(B_519))), inference(resolution, [status(thm)], [c_84, c_7869])).
% 14.43/5.72  tff(c_7979, plain, (![A_525, B_526]: (k1_partfun1('#skF_2', '#skF_2', A_525, A_525, '#skF_3', k2_funct_2(A_525, B_526))=k5_relat_1('#skF_3', k2_funct_2(A_525, B_526)) | ~v1_funct_1(k2_funct_2(A_525, B_526)) | ~m1_subset_1(B_526, k1_zfmisc_1(k2_zfmisc_1(A_525, A_525))) | ~v3_funct_2(B_526, A_525, A_525) | ~v1_funct_2(B_526, A_525, A_525) | ~v1_funct_1(B_526))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_7892])).
% 14.43/5.72  tff(c_8002, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3'))=k5_relat_1('#skF_3', k2_funct_2('#skF_2', '#skF_3')) | ~v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_7979])).
% 14.43/5.72  tff(c_8029, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_1359, c_1358, c_1358, c_1358, c_8002])).
% 14.43/5.72  tff(c_1360, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3')), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1358, c_140])).
% 14.43/5.72  tff(c_8187, plain, (~r2_relset_1('#skF_2', '#skF_2', k5_relat_1('#skF_3', k2_funct_1('#skF_3')), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_8029, c_1360])).
% 14.43/5.72  tff(c_8194, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1(k1_relat_1('#skF_3')), k6_partfun1('#skF_2')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_91, c_8187])).
% 14.43/5.72  tff(c_8200, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_166, c_90, c_803, c_1268, c_1152, c_8194])).
% 14.43/5.72  tff(c_8202, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_275])).
% 14.43/5.72  tff(c_203, plain, (k2_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_166, c_6])).
% 14.43/5.72  tff(c_247, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_203])).
% 14.43/5.72  tff(c_8209, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_8202, c_247])).
% 14.43/5.72  tff(c_248, plain, (![C_71, B_72, A_73]: (v5_relat_1(C_71, B_72) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_73, B_72))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 14.43/5.72  tff(c_266, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_84, c_248])).
% 14.43/5.72  tff(c_8313, plain, (![B_547, A_548]: (k2_relat_1(B_547)=A_548 | ~v2_funct_2(B_547, A_548) | ~v5_relat_1(B_547, A_548) | ~v1_relat_1(B_547))), inference(cnfTransformation, [status(thm)], [f_113])).
% 14.43/5.72  tff(c_8322, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_266, c_8313])).
% 14.43/5.72  tff(c_8334, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_166, c_8322])).
% 14.43/5.72  tff(c_8335, plain, (~v2_funct_2('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_8209, c_8334])).
% 14.43/5.72  tff(c_8531, plain, (![C_578, B_579, A_580]: (v2_funct_2(C_578, B_579) | ~v3_funct_2(C_578, A_580, B_579) | ~v1_funct_1(C_578) | ~m1_subset_1(C_578, k1_zfmisc_1(k2_zfmisc_1(A_580, B_579))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 14.43/5.72  tff(c_8544, plain, (v2_funct_2('#skF_3', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_8531])).
% 14.43/5.72  tff(c_8553, plain, (v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_86, c_8544])).
% 14.43/5.72  tff(c_8555, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8335, c_8553])).
% 14.43/5.72  tff(c_8556, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_203])).
% 14.43/5.72  tff(c_2, plain, (![A_1]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 14.43/5.72  tff(c_8566, plain, (![A_1]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_8556, c_2])).
% 14.43/5.72  tff(c_9551, plain, (![A_699, B_700, C_701, D_702]: (r2_relset_1(A_699, B_700, C_701, C_701) | ~m1_subset_1(D_702, k1_zfmisc_1(k2_zfmisc_1(A_699, B_700))) | ~m1_subset_1(C_701, k1_zfmisc_1(k2_zfmisc_1(A_699, B_700))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 14.43/5.72  tff(c_10601, plain, (![A_805, B_806, C_807]: (r2_relset_1(A_805, B_806, C_807, C_807) | ~m1_subset_1(C_807, k1_zfmisc_1(k2_zfmisc_1(A_805, B_806))))), inference(resolution, [status(thm)], [c_8566, c_9551])).
% 14.43/5.72  tff(c_10615, plain, (![A_805, B_806]: (r2_relset_1(A_805, B_806, '#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_8566, c_10601])).
% 14.43/5.72  tff(c_9266, plain, (![C_677, A_678, B_679]: (v2_funct_1(C_677) | ~v3_funct_2(C_677, A_678, B_679) | ~v1_funct_1(C_677) | ~m1_subset_1(C_677, k1_zfmisc_1(k2_zfmisc_1(A_678, B_679))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 14.43/5.72  tff(c_9270, plain, (![A_678, B_679]: (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', A_678, B_679) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_8566, c_9266])).
% 14.43/5.72  tff(c_9279, plain, (![A_678, B_679]: (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', A_678, B_679))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_9270])).
% 14.43/5.72  tff(c_9285, plain, (![A_678, B_679]: (~v3_funct_2('#skF_3', A_678, B_679))), inference(splitLeft, [status(thm)], [c_9279])).
% 14.43/5.72  tff(c_8595, plain, (![A_583]: (A_583!='#skF_3' | k6_partfun1(A_583)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8556, c_8556, c_214])).
% 14.43/5.72  tff(c_8601, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), '#skF_3') | '#skF_2'!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_8595, c_140])).
% 14.43/5.72  tff(c_8660, plain, ('#skF_2'!='#skF_3'), inference(splitLeft, [status(thm)], [c_8601])).
% 14.43/5.72  tff(c_8883, plain, (![C_629, B_630, A_631]: (v2_funct_2(C_629, B_630) | ~v3_funct_2(C_629, A_631, B_630) | ~v1_funct_1(C_629) | ~m1_subset_1(C_629, k1_zfmisc_1(k2_zfmisc_1(A_631, B_630))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 14.43/5.72  tff(c_8887, plain, (![B_630, A_631]: (v2_funct_2('#skF_3', B_630) | ~v3_funct_2('#skF_3', A_631, B_630) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_8566, c_8883])).
% 14.43/5.72  tff(c_9048, plain, (![B_643, A_644]: (v2_funct_2('#skF_3', B_643) | ~v3_funct_2('#skF_3', A_644, B_643))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_8887])).
% 14.43/5.72  tff(c_9056, plain, (v2_funct_2('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_86, c_9048])).
% 14.43/5.72  tff(c_8557, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_203])).
% 14.43/5.72  tff(c_8572, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8556, c_8557])).
% 14.43/5.72  tff(c_8638, plain, (![C_586, B_587, A_588]: (v5_relat_1(C_586, B_587) | ~m1_subset_1(C_586, k1_zfmisc_1(k2_zfmisc_1(A_588, B_587))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 14.43/5.72  tff(c_8649, plain, (![B_587]: (v5_relat_1('#skF_3', B_587))), inference(resolution, [status(thm)], [c_8566, c_8638])).
% 14.43/5.72  tff(c_8736, plain, (![B_604, A_605]: (k2_relat_1(B_604)=A_605 | ~v2_funct_2(B_604, A_605) | ~v5_relat_1(B_604, A_605) | ~v1_relat_1(B_604))), inference(cnfTransformation, [status(thm)], [f_113])).
% 14.43/5.72  tff(c_8742, plain, (![B_587]: (k2_relat_1('#skF_3')=B_587 | ~v2_funct_2('#skF_3', B_587) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_8649, c_8736])).
% 14.43/5.72  tff(c_8751, plain, (![B_587]: (B_587='#skF_3' | ~v2_funct_2('#skF_3', B_587))), inference(demodulation, [status(thm), theory('equality')], [c_166, c_8572, c_8742])).
% 14.43/5.72  tff(c_9059, plain, ('#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_9056, c_8751])).
% 14.43/5.72  tff(c_9063, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8660, c_9059])).
% 14.43/5.72  tff(c_9065, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_8601])).
% 14.43/5.72  tff(c_9067, plain, (v3_funct_2('#skF_3', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9065, c_9065, c_86])).
% 14.43/5.72  tff(c_9287, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9285, c_9067])).
% 14.43/5.72  tff(c_9288, plain, (v2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_9279])).
% 14.43/5.72  tff(c_8594, plain, (k6_partfun1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8556, c_8556, c_214])).
% 14.43/5.72  tff(c_218, plain, (![A_70]: (k1_xboole_0!=A_70 | k6_partfun1(A_70)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_93, c_210])).
% 14.43/5.72  tff(c_10, plain, (![A_6]: (k1_relat_1(k6_relat_1(A_6))=A_6)), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.43/5.72  tff(c_94, plain, (![A_6]: (k1_relat_1(k6_partfun1(A_6))=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_80, c_10])).
% 14.43/5.72  tff(c_232, plain, (![A_70]: (k1_relat_1(k1_xboole_0)=A_70 | k1_xboole_0!=A_70)), inference(superposition, [status(thm), theory('equality')], [c_218, c_94])).
% 14.43/5.72  tff(c_8629, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8556, c_8556, c_232])).
% 14.43/5.72  tff(c_66, plain, (![A_32]: (v1_funct_1('#skF_1'(A_32)))), inference(cnfTransformation, [status(thm)], [f_148])).
% 14.43/5.72  tff(c_62, plain, (![A_32]: (v3_funct_2('#skF_1'(A_32), A_32, A_32))), inference(cnfTransformation, [status(thm)], [f_148])).
% 14.43/5.72  tff(c_9411, plain, (![C_688, B_689, A_690]: (v2_funct_2(C_688, B_689) | ~v3_funct_2(C_688, A_690, B_689) | ~v1_funct_1(C_688) | ~m1_subset_1(C_688, k1_zfmisc_1(k2_zfmisc_1(A_690, B_689))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 14.43/5.72  tff(c_9421, plain, (![A_32]: (v2_funct_2('#skF_1'(A_32), A_32) | ~v3_funct_2('#skF_1'(A_32), A_32, A_32) | ~v1_funct_1('#skF_1'(A_32)))), inference(resolution, [status(thm)], [c_74, c_9411])).
% 14.43/5.72  tff(c_9429, plain, (![A_32]: (v2_funct_2('#skF_1'(A_32), A_32))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_9421])).
% 14.43/5.72  tff(c_72, plain, (![A_32]: (v1_relat_1('#skF_1'(A_32)))), inference(cnfTransformation, [status(thm)], [f_148])).
% 14.43/5.72  tff(c_68, plain, (![A_32]: (v5_relat_1('#skF_1'(A_32), A_32))), inference(cnfTransformation, [status(thm)], [f_148])).
% 14.43/5.72  tff(c_9145, plain, (![B_660, A_661]: (k2_relat_1(B_660)=A_661 | ~v2_funct_2(B_660, A_661) | ~v5_relat_1(B_660, A_661) | ~v1_relat_1(B_660))), inference(cnfTransformation, [status(thm)], [f_113])).
% 14.43/5.72  tff(c_9154, plain, (![A_32]: (k2_relat_1('#skF_1'(A_32))=A_32 | ~v2_funct_2('#skF_1'(A_32), A_32) | ~v1_relat_1('#skF_1'(A_32)))), inference(resolution, [status(thm)], [c_68, c_9145])).
% 14.43/5.72  tff(c_9163, plain, (![A_32]: (k2_relat_1('#skF_1'(A_32))=A_32 | ~v2_funct_2('#skF_1'(A_32), A_32))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_9154])).
% 14.43/5.72  tff(c_9431, plain, (![A_32]: (k2_relat_1('#skF_1'(A_32))=A_32)), inference(demodulation, [status(thm), theory('equality')], [c_9429, c_9163])).
% 14.43/5.72  tff(c_133, plain, (![A_55]: (k2_relat_1(A_55)!=k1_xboole_0 | k1_xboole_0=A_55 | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_41])).
% 14.43/5.72  tff(c_137, plain, (![A_32]: (k2_relat_1('#skF_1'(A_32))!=k1_xboole_0 | '#skF_1'(A_32)=k1_xboole_0)), inference(resolution, [status(thm)], [c_72, c_133])).
% 14.43/5.72  tff(c_8562, plain, (![A_32]: (k2_relat_1('#skF_1'(A_32))!='#skF_3' | '#skF_1'(A_32)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8556, c_8556, c_137])).
% 14.43/5.72  tff(c_9437, plain, (![A_32]: (A_32!='#skF_3' | '#skF_1'(A_32)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9431, c_8562])).
% 14.43/5.72  tff(c_64, plain, (![A_32]: (v1_funct_2('#skF_1'(A_32), A_32, A_32))), inference(cnfTransformation, [status(thm)], [f_148])).
% 14.43/5.72  tff(c_9695, plain, (![A_725, B_726]: (k2_funct_2(A_725, B_726)=k2_funct_1(B_726) | ~m1_subset_1(B_726, k1_zfmisc_1(k2_zfmisc_1(A_725, A_725))) | ~v3_funct_2(B_726, A_725, A_725) | ~v1_funct_2(B_726, A_725, A_725) | ~v1_funct_1(B_726))), inference(cnfTransformation, [status(thm)], [f_168])).
% 14.43/5.72  tff(c_9705, plain, (![A_32]: (k2_funct_2(A_32, '#skF_1'(A_32))=k2_funct_1('#skF_1'(A_32)) | ~v3_funct_2('#skF_1'(A_32), A_32, A_32) | ~v1_funct_2('#skF_1'(A_32), A_32, A_32) | ~v1_funct_1('#skF_1'(A_32)))), inference(resolution, [status(thm)], [c_74, c_9695])).
% 14.43/5.72  tff(c_9712, plain, (![A_32]: (k2_funct_2(A_32, '#skF_1'(A_32))=k2_funct_1('#skF_1'(A_32)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_9705])).
% 14.43/5.72  tff(c_9868, plain, (![A_746, B_747]: (m1_subset_1(k2_funct_2(A_746, B_747), k1_zfmisc_1(k2_zfmisc_1(A_746, A_746))) | ~m1_subset_1(B_747, k1_zfmisc_1(k2_zfmisc_1(A_746, A_746))) | ~v3_funct_2(B_747, A_746, A_746) | ~v1_funct_2(B_747, A_746, A_746) | ~v1_funct_1(B_747))), inference(cnfTransformation, [status(thm)], [f_129])).
% 14.43/5.72  tff(c_9923, plain, (![A_32]: (m1_subset_1(k2_funct_1('#skF_1'(A_32)), k1_zfmisc_1(k2_zfmisc_1(A_32, A_32))) | ~m1_subset_1('#skF_1'(A_32), k1_zfmisc_1(k2_zfmisc_1(A_32, A_32))) | ~v3_funct_2('#skF_1'(A_32), A_32, A_32) | ~v1_funct_2('#skF_1'(A_32), A_32, A_32) | ~v1_funct_1('#skF_1'(A_32)))), inference(superposition, [status(thm), theory('equality')], [c_9712, c_9868])).
% 14.43/5.72  tff(c_9945, plain, (![A_748]: (m1_subset_1(k2_funct_1('#skF_1'(A_748)), k1_zfmisc_1(k2_zfmisc_1(A_748, A_748))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_74, c_9923])).
% 14.43/5.72  tff(c_18, plain, (![C_10, A_8, B_9]: (v1_relat_1(C_10) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 14.43/5.72  tff(c_10048, plain, (![A_750]: (v1_relat_1(k2_funct_1('#skF_1'(A_750))))), inference(resolution, [status(thm)], [c_9945, c_18])).
% 14.43/5.72  tff(c_10058, plain, (![A_32]: (v1_relat_1(k2_funct_1('#skF_3')) | A_32!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_9437, c_10048])).
% 14.43/5.72  tff(c_10111, plain, (![A_32]: (A_32!='#skF_3')), inference(splitLeft, [status(thm)], [c_10058])).
% 14.43/5.72  tff(c_9179, plain, (![A_666, B_667, C_668]: (k1_relset_1(A_666, B_667, C_668)=k1_relat_1(C_668) | ~m1_subset_1(C_668, k1_zfmisc_1(k2_zfmisc_1(A_666, B_667))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 14.43/5.72  tff(c_9183, plain, (![A_666, B_667]: (k1_relset_1(A_666, B_667, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_8566, c_9179])).
% 14.43/5.72  tff(c_9191, plain, (![A_666, B_667]: (k1_relset_1(A_666, B_667, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8629, c_9183])).
% 14.43/5.72  tff(c_10132, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10111, c_9191])).
% 14.43/5.72  tff(c_10133, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_10058])).
% 14.43/5.72  tff(c_8, plain, (![A_5]: (k1_relat_1(A_5)!=k1_xboole_0 | k1_xboole_0=A_5 | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 14.43/5.72  tff(c_8563, plain, (![A_5]: (k1_relat_1(A_5)!='#skF_3' | A_5='#skF_3' | ~v1_relat_1(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_8556, c_8556, c_8])).
% 14.43/5.72  tff(c_10141, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_3' | k2_funct_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_10133, c_8563])).
% 14.43/5.72  tff(c_10242, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_10141])).
% 14.43/5.72  tff(c_9834, plain, (![A_739, B_740]: (v1_funct_2(k2_funct_2(A_739, B_740), A_739, A_739) | ~m1_subset_1(B_740, k1_zfmisc_1(k2_zfmisc_1(A_739, A_739))) | ~v3_funct_2(B_740, A_739, A_739) | ~v1_funct_2(B_740, A_739, A_739) | ~v1_funct_1(B_740))), inference(cnfTransformation, [status(thm)], [f_129])).
% 14.43/5.72  tff(c_9841, plain, (![A_32]: (v1_funct_2(k2_funct_2(A_32, '#skF_1'(A_32)), A_32, A_32) | ~v3_funct_2('#skF_1'(A_32), A_32, A_32) | ~v1_funct_2('#skF_1'(A_32), A_32, A_32) | ~v1_funct_1('#skF_1'(A_32)))), inference(resolution, [status(thm)], [c_74, c_9834])).
% 14.43/5.72  tff(c_9849, plain, (![A_741]: (v1_funct_2(k2_funct_1('#skF_1'(A_741)), A_741, A_741))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_9712, c_9841])).
% 14.43/5.72  tff(c_9856, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_9437, c_9849])).
% 14.43/5.72  tff(c_10404, plain, (![A_797]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(A_797, A_797))) | A_797!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_9437, c_9945])).
% 14.43/5.72  tff(c_42, plain, (![B_25, C_26]: (k1_relset_1(k1_xboole_0, B_25, C_26)=k1_xboole_0 | ~v1_funct_2(C_26, k1_xboole_0, B_25) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_25))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 14.43/5.72  tff(c_9289, plain, (![B_25, C_26]: (k1_relset_1('#skF_3', B_25, C_26)='#skF_3' | ~v1_funct_2(C_26, '#skF_3', B_25) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_25))))), inference(demodulation, [status(thm), theory('equality')], [c_8556, c_8556, c_8556, c_8556, c_42])).
% 14.43/5.72  tff(c_10437, plain, (k1_relset_1('#skF_3', '#skF_3', k2_funct_1('#skF_3'))='#skF_3' | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_10404, c_9289])).
% 14.43/5.72  tff(c_10487, plain, (k1_relset_1('#skF_3', '#skF_3', k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9856, c_10437])).
% 14.43/5.72  tff(c_24, plain, (![A_14, B_15, C_16]: (k1_relset_1(A_14, B_15, C_16)=k1_relat_1(C_16) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 14.43/5.72  tff(c_10495, plain, (![A_797]: (k1_relset_1(A_797, A_797, k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3')) | A_797!='#skF_3')), inference(resolution, [status(thm)], [c_10404, c_24])).
% 14.43/5.72  tff(c_10514, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_10487, c_10495])).
% 14.43/5.72  tff(c_10523, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10242, c_10514])).
% 14.43/5.72  tff(c_10524, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_10141])).
% 14.43/5.72  tff(c_10543, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k5_relat_1('#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10524, c_91])).
% 14.43/5.72  tff(c_10550, plain, (k5_relat_1('#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_166, c_90, c_9288, c_8594, c_8629, c_10543])).
% 14.43/5.72  tff(c_10061, plain, (![C_756, F_753, E_754, A_751, D_752, B_755]: (k1_partfun1(A_751, B_755, C_756, D_752, E_754, F_753)=k5_relat_1(E_754, F_753) | ~m1_subset_1(F_753, k1_zfmisc_1(k2_zfmisc_1(C_756, D_752))) | ~v1_funct_1(F_753) | ~m1_subset_1(E_754, k1_zfmisc_1(k2_zfmisc_1(A_751, B_755))) | ~v1_funct_1(E_754))), inference(cnfTransformation, [status(thm)], [f_158])).
% 14.43/5.72  tff(c_10072, plain, (![A_751, B_755, A_32, E_754]: (k1_partfun1(A_751, B_755, A_32, A_32, E_754, '#skF_1'(A_32))=k5_relat_1(E_754, '#skF_1'(A_32)) | ~v1_funct_1('#skF_1'(A_32)) | ~m1_subset_1(E_754, k1_zfmisc_1(k2_zfmisc_1(A_751, B_755))) | ~v1_funct_1(E_754))), inference(resolution, [status(thm)], [c_74, c_10061])).
% 14.43/5.72  tff(c_10560, plain, (![A_799, B_800, A_801, E_802]: (k1_partfun1(A_799, B_800, A_801, A_801, E_802, '#skF_1'(A_801))=k5_relat_1(E_802, '#skF_1'(A_801)) | ~m1_subset_1(E_802, k1_zfmisc_1(k2_zfmisc_1(A_799, B_800))) | ~v1_funct_1(E_802))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_10072])).
% 14.43/5.72  tff(c_10567, plain, (![A_799, B_800, A_801]: (k1_partfun1(A_799, B_800, A_801, A_801, '#skF_3', '#skF_1'(A_801))=k5_relat_1('#skF_3', '#skF_1'(A_801)) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_8566, c_10560])).
% 14.43/5.72  tff(c_16050, plain, (![A_1051, B_1052, A_1053]: (k1_partfun1(A_1051, B_1052, A_1053, A_1053, '#skF_3', '#skF_1'(A_1053))=k5_relat_1('#skF_3', '#skF_1'(A_1053)))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_10567])).
% 14.43/5.72  tff(c_19258, plain, (![A_1146, A_1147, B_1148]: (k5_relat_1('#skF_3', '#skF_1'(A_1146))=k1_partfun1(A_1147, B_1148, A_1146, A_1146, '#skF_3', '#skF_3') | A_1146!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_9437, c_16050])).
% 14.43/5.72  tff(c_19279, plain, (![A_1147, B_1148, A_32]: (k1_partfun1(A_1147, B_1148, A_32, A_32, '#skF_3', '#skF_3')=k5_relat_1('#skF_3', '#skF_3') | A_32!='#skF_3' | A_32!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_9437, c_19258])).
% 14.43/5.72  tff(c_19313, plain, (![A_1150, B_1151, A_1152]: (k1_partfun1(A_1150, B_1151, A_1152, A_1152, '#skF_3', '#skF_3')='#skF_3' | A_1152!='#skF_3' | A_1152!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10550, c_19279])).
% 14.43/5.72  tff(c_9714, plain, (![A_727]: (k2_funct_2(A_727, '#skF_1'(A_727))=k2_funct_1('#skF_1'(A_727)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_9705])).
% 14.43/5.72  tff(c_9723, plain, (![A_32]: (k2_funct_1('#skF_1'(A_32))=k2_funct_2(A_32, '#skF_3') | A_32!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_9437, c_9714])).
% 14.43/5.72  tff(c_11031, plain, (![A_842]: (k1_relat_1(k2_funct_1('#skF_1'(A_842)))!='#skF_3' | k2_funct_1('#skF_1'(A_842))='#skF_3')), inference(resolution, [status(thm)], [c_10048, c_8563])).
% 14.43/5.72  tff(c_11040, plain, (![A_32]: (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_3' | k2_funct_1('#skF_1'(A_32))='#skF_3' | A_32!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_9437, c_11031])).
% 14.43/5.72  tff(c_11044, plain, (![A_843]: (k2_funct_1('#skF_1'(A_843))='#skF_3' | A_843!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8629, c_10524, c_11040])).
% 14.43/5.72  tff(c_11219, plain, (![A_846]: (k2_funct_2(A_846, '#skF_3')='#skF_3' | A_846!='#skF_3' | A_846!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_9723, c_11044])).
% 14.43/5.72  tff(c_9066, plain, (~r2_relset_1('#skF_3', '#skF_3', k1_partfun1('#skF_3', '#skF_3', '#skF_3', '#skF_3', '#skF_3', k2_funct_2('#skF_3', '#skF_3')), k6_partfun1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_9065, c_9065, c_9065, c_9065, c_9065, c_9065, c_9065, c_9065, c_140])).
% 14.43/5.72  tff(c_9069, plain, (~r2_relset_1('#skF_3', '#skF_3', k1_partfun1('#skF_3', '#skF_3', '#skF_3', '#skF_3', '#skF_3', k2_funct_2('#skF_3', '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8594, c_9066])).
% 14.43/5.72  tff(c_11308, plain, (~r2_relset_1('#skF_3', '#skF_3', k1_partfun1('#skF_3', '#skF_3', '#skF_3', '#skF_3', '#skF_3', '#skF_3'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_11219, c_9069])).
% 14.43/5.72  tff(c_19322, plain, (~r2_relset_1('#skF_3', '#skF_3', '#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_19313, c_11308])).
% 14.43/5.72  tff(c_19333, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10615, c_19322])).
% 14.43/5.72  tff(c_19334, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(splitRight, [status(thm)], [c_82])).
% 14.43/5.72  tff(c_20572, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_20569, c_19334])).
% 14.43/5.72  tff(c_21408, plain, (~r2_relset_1('#skF_2', '#skF_2', k5_relat_1(k2_funct_1('#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_21347, c_20572])).
% 14.43/5.72  tff(c_21444, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1(k2_relat_1('#skF_3')), k6_partfun1('#skF_2')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_92, c_21408])).
% 14.43/5.72  tff(c_21450, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_19361, c_90, c_19837, c_20701, c_19709, c_21444])).
% 14.43/5.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.43/5.72  
% 14.43/5.72  Inference rules
% 14.43/5.72  ----------------------
% 14.43/5.72  #Ref     : 7
% 14.43/5.72  #Sup     : 4981
% 14.43/5.72  #Fact    : 0
% 14.43/5.72  #Define  : 0
% 14.43/5.72  #Split   : 45
% 14.43/5.72  #Chain   : 0
% 14.43/5.72  #Close   : 0
% 14.43/5.72  
% 14.43/5.72  Ordering : KBO
% 14.43/5.72  
% 14.43/5.72  Simplification rules
% 14.43/5.72  ----------------------
% 14.43/5.72  #Subsume      : 1666
% 14.43/5.72  #Demod        : 5492
% 14.43/5.72  #Tautology    : 1792
% 14.43/5.72  #SimpNegUnit  : 298
% 14.43/5.72  #BackRed      : 318
% 14.43/5.72  
% 14.43/5.72  #Partial instantiations: 0
% 14.43/5.72  #Strategies tried      : 1
% 14.43/5.72  
% 14.43/5.72  Timing (in seconds)
% 14.43/5.72  ----------------------
% 14.43/5.72  Preprocessing        : 0.38
% 14.43/5.72  Parsing              : 0.20
% 14.43/5.72  CNF conversion       : 0.03
% 14.43/5.72  Main loop            : 4.52
% 14.43/5.72  Inferencing          : 1.24
% 14.43/5.72  Reduction            : 2.14
% 14.43/5.72  Demodulation         : 1.72
% 14.43/5.72  BG Simplification    : 0.09
% 14.43/5.72  Subsumption          : 0.80
% 14.43/5.72  Abstraction          : 0.13
% 14.43/5.72  MUC search           : 0.00
% 14.43/5.72  Cooper               : 0.00
% 14.43/5.72  Total                : 4.98
% 14.43/5.72  Index Insertion      : 0.00
% 14.43/5.72  Index Deletion       : 0.00
% 14.43/5.72  Index Matching       : 0.00
% 14.43/5.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
