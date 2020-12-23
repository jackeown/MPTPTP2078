%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:01 EST 2020

% Result     : Theorem 10.08s
% Output     : CNFRefutation 10.19s
% Verified   : 
% Statistics : Number of formulae       :  273 (8133 expanded)
%              Number of leaves         :   48 (2454 expanded)
%              Depth                    :   23
%              Number of atoms          :  572 (19521 expanded)
%              Number of equality atoms :  143 (8125 expanded)
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

tff(f_171,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_136,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_116,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_158,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_56,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_156,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_132,axiom,(
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

tff(f_146,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_108,axiom,(
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

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_46,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_82,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_12257,plain,(
    ! [C_1027,A_1028,B_1029] :
      ( v1_relat_1(C_1027)
      | ~ m1_subset_1(C_1027,k1_zfmisc_1(k2_zfmisc_1(A_1028,B_1029))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_12274,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_82,c_12257])).

tff(c_88,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_84,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_12843,plain,(
    ! [C_1115,A_1116,B_1117] :
      ( v2_funct_1(C_1115)
      | ~ v3_funct_2(C_1115,A_1116,B_1117)
      | ~ v1_funct_1(C_1115)
      | ~ m1_subset_1(C_1115,k1_zfmisc_1(k2_zfmisc_1(A_1116,B_1117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_12856,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_82,c_12843])).

tff(c_12864,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_84,c_12856])).

tff(c_72,plain,(
    ! [A_32] : m1_subset_1(k6_partfun1(A_32),k1_zfmisc_1(k2_zfmisc_1(A_32,A_32))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_12480,plain,(
    ! [A_1064,B_1065,D_1066] :
      ( r2_relset_1(A_1064,B_1065,D_1066,D_1066)
      | ~ m1_subset_1(D_1066,k1_zfmisc_1(k2_zfmisc_1(A_1064,B_1065))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_12492,plain,(
    ! [A_32] : r2_relset_1(A_32,A_32,k6_partfun1(A_32),k6_partfun1(A_32)) ),
    inference(resolution,[status(thm)],[c_72,c_12480])).

tff(c_12384,plain,(
    ! [C_1048,B_1049,A_1050] :
      ( v5_relat_1(C_1048,B_1049)
      | ~ m1_subset_1(C_1048,k1_zfmisc_1(k2_zfmisc_1(A_1050,B_1049))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_12403,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_82,c_12384])).

tff(c_12514,plain,(
    ! [B_1070,A_1071] :
      ( k2_relat_1(B_1070) = A_1071
      | ~ v2_funct_2(B_1070,A_1071)
      | ~ v5_relat_1(B_1070,A_1071)
      | ~ v1_relat_1(B_1070) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_12526,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_12403,c_12514])).

tff(c_12536,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12274,c_12526])).

tff(c_12543,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_12536])).

tff(c_12723,plain,(
    ! [C_1103,B_1104,A_1105] :
      ( v2_funct_2(C_1103,B_1104)
      | ~ v3_funct_2(C_1103,A_1105,B_1104)
      | ~ v1_funct_1(C_1103)
      | ~ m1_subset_1(C_1103,k1_zfmisc_1(k2_zfmisc_1(A_1105,B_1104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_12736,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_82,c_12723])).

tff(c_12744,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_84,c_12736])).

tff(c_12746,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12543,c_12744])).

tff(c_12747,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_12536])).

tff(c_78,plain,(
    ! [A_41] : k6_relat_1(A_41) = k6_partfun1(A_41) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_24,plain,(
    ! [A_8] :
      ( k5_relat_1(k2_funct_1(A_8),A_8) = k6_relat_1(k2_relat_1(A_8))
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_90,plain,(
    ! [A_8] :
      ( k5_relat_1(k2_funct_1(A_8),A_8) = k6_partfun1(k2_relat_1(A_8))
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_24])).

tff(c_86,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_13428,plain,(
    ! [A_1207,B_1208] :
      ( k2_funct_2(A_1207,B_1208) = k2_funct_1(B_1208)
      | ~ m1_subset_1(B_1208,k1_zfmisc_1(k2_zfmisc_1(A_1207,A_1207)))
      | ~ v3_funct_2(B_1208,A_1207,A_1207)
      | ~ v1_funct_2(B_1208,A_1207,A_1207)
      | ~ v1_funct_1(B_1208) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_13442,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_82,c_13428])).

tff(c_13451,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_84,c_13442])).

tff(c_13329,plain,(
    ! [A_1189,B_1190] :
      ( v1_funct_1(k2_funct_2(A_1189,B_1190))
      | ~ m1_subset_1(B_1190,k1_zfmisc_1(k2_zfmisc_1(A_1189,A_1189)))
      | ~ v3_funct_2(B_1190,A_1189,A_1189)
      | ~ v1_funct_2(B_1190,A_1189,A_1189)
      | ~ v1_funct_1(B_1190) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_13343,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_82,c_13329])).

tff(c_13352,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_84,c_13343])).

tff(c_13452,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13451,c_13352])).

tff(c_62,plain,(
    ! [A_30,B_31] :
      ( m1_subset_1(k2_funct_2(A_30,B_31),k1_zfmisc_1(k2_zfmisc_1(A_30,A_30)))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(k2_zfmisc_1(A_30,A_30)))
      | ~ v3_funct_2(B_31,A_30,A_30)
      | ~ v1_funct_2(B_31,A_30,A_30)
      | ~ v1_funct_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_13827,plain,(
    ! [C_1239,B_1242,D_1241,F_1240,E_1238,A_1237] :
      ( k1_partfun1(A_1237,B_1242,C_1239,D_1241,E_1238,F_1240) = k5_relat_1(E_1238,F_1240)
      | ~ m1_subset_1(F_1240,k1_zfmisc_1(k2_zfmisc_1(C_1239,D_1241)))
      | ~ v1_funct_1(F_1240)
      | ~ m1_subset_1(E_1238,k1_zfmisc_1(k2_zfmisc_1(A_1237,B_1242)))
      | ~ v1_funct_1(E_1238) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_13840,plain,(
    ! [A_1237,B_1242,E_1238] :
      ( k1_partfun1(A_1237,B_1242,'#skF_1','#skF_1',E_1238,'#skF_2') = k5_relat_1(E_1238,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_1238,k1_zfmisc_1(k2_zfmisc_1(A_1237,B_1242)))
      | ~ v1_funct_1(E_1238) ) ),
    inference(resolution,[status(thm)],[c_82,c_13827])).

tff(c_13866,plain,(
    ! [A_1243,B_1244,E_1245] :
      ( k1_partfun1(A_1243,B_1244,'#skF_1','#skF_1',E_1245,'#skF_2') = k5_relat_1(E_1245,'#skF_2')
      | ~ m1_subset_1(E_1245,k1_zfmisc_1(k2_zfmisc_1(A_1243,B_1244)))
      | ~ v1_funct_1(E_1245) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_13840])).

tff(c_14437,plain,(
    ! [A_1259,B_1260] :
      ( k1_partfun1(A_1259,A_1259,'#skF_1','#skF_1',k2_funct_2(A_1259,B_1260),'#skF_2') = k5_relat_1(k2_funct_2(A_1259,B_1260),'#skF_2')
      | ~ v1_funct_1(k2_funct_2(A_1259,B_1260))
      | ~ m1_subset_1(B_1260,k1_zfmisc_1(k2_zfmisc_1(A_1259,A_1259)))
      | ~ v3_funct_2(B_1260,A_1259,A_1259)
      | ~ v1_funct_2(B_1260,A_1259,A_1259)
      | ~ v1_funct_1(B_1260) ) ),
    inference(resolution,[status(thm)],[c_62,c_13866])).

tff(c_14455,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2') = k5_relat_1(k2_funct_2('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_82,c_14437])).

tff(c_14473,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2') = k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_84,c_13452,c_13451,c_13451,c_13451,c_14455])).

tff(c_228,plain,(
    ! [C_58,A_59,B_60] :
      ( v1_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_245,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_82,c_228])).

tff(c_873,plain,(
    ! [C_157,A_158,B_159] :
      ( v2_funct_1(C_157)
      | ~ v3_funct_2(C_157,A_158,B_159)
      | ~ v1_funct_1(C_157)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_158,B_159))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_886,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_82,c_873])).

tff(c_894,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_84,c_886])).

tff(c_749,plain,(
    ! [A_139,B_140,D_141] :
      ( r2_relset_1(A_139,B_140,D_141,D_141)
      | ~ m1_subset_1(D_141,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_761,plain,(
    ! [A_32] : r2_relset_1(A_32,A_32,k6_partfun1(A_32),k6_partfun1(A_32)) ),
    inference(resolution,[status(thm)],[c_72,c_749])).

tff(c_773,plain,(
    ! [A_143,B_144,C_145] :
      ( k1_relset_1(A_143,B_144,C_145) = k1_relat_1(C_145)
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(A_143,B_144))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_792,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_82,c_773])).

tff(c_1070,plain,(
    ! [B_191,A_192,C_193] :
      ( k1_xboole_0 = B_191
      | k1_relset_1(A_192,B_191,C_193) = A_192
      | ~ v1_funct_2(C_193,A_192,B_191)
      | ~ m1_subset_1(C_193,k1_zfmisc_1(k2_zfmisc_1(A_192,B_191))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1083,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_82,c_1070])).

tff(c_1093,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_792,c_1083])).

tff(c_1094,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1093])).

tff(c_26,plain,(
    ! [A_8] :
      ( k5_relat_1(A_8,k2_funct_1(A_8)) = k6_relat_1(k1_relat_1(A_8))
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_89,plain,(
    ! [A_8] :
      ( k5_relat_1(A_8,k2_funct_1(A_8)) = k6_partfun1(k1_relat_1(A_8))
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_26])).

tff(c_1403,plain,(
    ! [A_239,B_240] :
      ( k2_funct_2(A_239,B_240) = k2_funct_1(B_240)
      | ~ m1_subset_1(B_240,k1_zfmisc_1(k2_zfmisc_1(A_239,A_239)))
      | ~ v3_funct_2(B_240,A_239,A_239)
      | ~ v1_funct_2(B_240,A_239,A_239)
      | ~ v1_funct_1(B_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_1417,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_82,c_1403])).

tff(c_1426,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_84,c_1417])).

tff(c_1377,plain,(
    ! [A_233,B_234] :
      ( v1_funct_1(k2_funct_2(A_233,B_234))
      | ~ m1_subset_1(B_234,k1_zfmisc_1(k2_zfmisc_1(A_233,A_233)))
      | ~ v3_funct_2(B_234,A_233,A_233)
      | ~ v1_funct_2(B_234,A_233,A_233)
      | ~ v1_funct_1(B_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1391,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_82,c_1377])).

tff(c_1400,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_84,c_1391])).

tff(c_1427,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1426,c_1400])).

tff(c_1519,plain,(
    ! [A_258,B_259] :
      ( m1_subset_1(k2_funct_2(A_258,B_259),k1_zfmisc_1(k2_zfmisc_1(A_258,A_258)))
      | ~ m1_subset_1(B_259,k1_zfmisc_1(k2_zfmisc_1(A_258,A_258)))
      | ~ v3_funct_2(B_259,A_258,A_258)
      | ~ v1_funct_2(B_259,A_258,A_258)
      | ~ v1_funct_1(B_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1561,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1426,c_1519])).

tff(c_1585,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_84,c_82,c_1561])).

tff(c_1715,plain,(
    ! [D_264,A_260,B_265,E_261,F_263,C_262] :
      ( k1_partfun1(A_260,B_265,C_262,D_264,E_261,F_263) = k5_relat_1(E_261,F_263)
      | ~ m1_subset_1(F_263,k1_zfmisc_1(k2_zfmisc_1(C_262,D_264)))
      | ~ v1_funct_1(F_263)
      | ~ m1_subset_1(E_261,k1_zfmisc_1(k2_zfmisc_1(A_260,B_265)))
      | ~ v1_funct_1(E_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_1717,plain,(
    ! [A_260,B_265,E_261] :
      ( k1_partfun1(A_260,B_265,'#skF_1','#skF_1',E_261,k2_funct_1('#skF_2')) = k5_relat_1(E_261,k2_funct_1('#skF_2'))
      | ~ v1_funct_1(k2_funct_1('#skF_2'))
      | ~ m1_subset_1(E_261,k1_zfmisc_1(k2_zfmisc_1(A_260,B_265)))
      | ~ v1_funct_1(E_261) ) ),
    inference(resolution,[status(thm)],[c_1585,c_1715])).

tff(c_4778,plain,(
    ! [A_368,B_369,E_370] :
      ( k1_partfun1(A_368,B_369,'#skF_1','#skF_1',E_370,k2_funct_1('#skF_2')) = k5_relat_1(E_370,k2_funct_1('#skF_2'))
      | ~ m1_subset_1(E_370,k1_zfmisc_1(k2_zfmisc_1(A_368,B_369)))
      | ~ v1_funct_1(E_370) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1427,c_1717])).

tff(c_4818,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2'))
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_82,c_4778])).

tff(c_4851,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_4818])).

tff(c_80,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1'))
    | ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_166,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_1428,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1426,c_166])).

tff(c_4852,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4851,c_1428])).

tff(c_4859,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k1_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_4852])).

tff(c_4862,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_245,c_88,c_894,c_761,c_1094,c_4859])).

tff(c_4863,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1093])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4898,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4863,c_8])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4897,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4863,c_4863,c_14])).

tff(c_139,plain,(
    ! [A_50,B_51] :
      ( r1_tarski(A_50,B_51)
      | ~ m1_subset_1(A_50,k1_zfmisc_1(B_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_147,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_82,c_139])).

tff(c_189,plain,(
    ! [B_56,A_57] :
      ( B_56 = A_57
      | ~ r1_tarski(B_56,A_57)
      | ~ r1_tarski(A_57,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_204,plain,
    ( k2_zfmisc_1('#skF_1','#skF_1') = '#skF_2'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_147,c_189])).

tff(c_316,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_204])).

tff(c_5033,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4897,c_316])).

tff(c_5038,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4898,c_5033])).

tff(c_5039,plain,(
    k2_zfmisc_1('#skF_1','#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_204])).

tff(c_5042,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5039,c_82])).

tff(c_6238,plain,(
    ! [C_558,A_559,B_560] :
      ( v2_funct_1(C_558)
      | ~ v3_funct_2(C_558,A_559,B_560)
      | ~ v1_funct_1(C_558)
      | ~ m1_subset_1(C_558,k1_zfmisc_1(k2_zfmisc_1(A_559,B_560))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_6353,plain,(
    ! [C_574] :
      ( v2_funct_1(C_574)
      | ~ v3_funct_2(C_574,'#skF_1','#skF_1')
      | ~ v1_funct_1(C_574)
      | ~ m1_subset_1(C_574,k1_zfmisc_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5039,c_6238])).

tff(c_6359,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_5042,c_6353])).

tff(c_6367,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_84,c_6359])).

tff(c_5257,plain,(
    ! [A_410,B_411,D_412] :
      ( r2_relset_1(A_410,B_411,D_412,D_412)
      | ~ m1_subset_1(D_412,k1_zfmisc_1(k2_zfmisc_1(A_410,B_411))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_5269,plain,(
    ! [A_32] : r2_relset_1(A_32,A_32,k6_partfun1(A_32),k6_partfun1(A_32)) ),
    inference(resolution,[status(thm)],[c_72,c_5257])).

tff(c_6089,plain,(
    ! [A_541,B_542,C_543] :
      ( k1_relset_1(A_541,B_542,C_543) = k1_relat_1(C_543)
      | ~ m1_subset_1(C_543,k1_zfmisc_1(k2_zfmisc_1(A_541,B_542))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_6134,plain,(
    ! [C_547] :
      ( k1_relset_1('#skF_1','#skF_1',C_547) = k1_relat_1(C_547)
      | ~ m1_subset_1(C_547,k1_zfmisc_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5039,c_6089])).

tff(c_6147,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_5042,c_6134])).

tff(c_6499,plain,(
    ! [B_601,A_602,C_603] :
      ( k1_xboole_0 = B_601
      | k1_relset_1(A_602,B_601,C_603) = A_602
      | ~ v1_funct_2(C_603,A_602,B_601)
      | ~ m1_subset_1(C_603,k1_zfmisc_1(k2_zfmisc_1(A_602,B_601))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_6502,plain,(
    ! [C_603] :
      ( k1_xboole_0 = '#skF_1'
      | k1_relset_1('#skF_1','#skF_1',C_603) = '#skF_1'
      | ~ v1_funct_2(C_603,'#skF_1','#skF_1')
      | ~ m1_subset_1(C_603,k1_zfmisc_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5039,c_6499])).

tff(c_6552,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_6502])).

tff(c_10,plain,(
    ! [B_5,A_4] :
      ( k1_xboole_0 = B_5
      | k1_xboole_0 = A_4
      | k2_zfmisc_1(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_5052,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_5039,c_10])).

tff(c_5099,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_5052])).

tff(c_6588,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6552,c_5099])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6597,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6552,c_6552,c_12])).

tff(c_6837,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6597,c_5039])).

tff(c_6839,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6588,c_6837])).

tff(c_6849,plain,(
    ! [C_621] :
      ( k1_relset_1('#skF_1','#skF_1',C_621) = '#skF_1'
      | ~ v1_funct_2(C_621,'#skF_1','#skF_1')
      | ~ m1_subset_1(C_621,k1_zfmisc_1('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_6502])).

tff(c_6855,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_5042,c_6849])).

tff(c_6864,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_6147,c_6855])).

tff(c_7322,plain,(
    ! [A_663,B_664] :
      ( k2_funct_2(A_663,B_664) = k2_funct_1(B_664)
      | ~ m1_subset_1(B_664,k1_zfmisc_1(k2_zfmisc_1(A_663,A_663)))
      | ~ v3_funct_2(B_664,A_663,A_663)
      | ~ v1_funct_2(B_664,A_663,A_663)
      | ~ v1_funct_1(B_664) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_7428,plain,(
    ! [B_675] :
      ( k2_funct_2('#skF_1',B_675) = k2_funct_1(B_675)
      | ~ m1_subset_1(B_675,k1_zfmisc_1('#skF_2'))
      | ~ v3_funct_2(B_675,'#skF_1','#skF_1')
      | ~ v1_funct_2(B_675,'#skF_1','#skF_1')
      | ~ v1_funct_1(B_675) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5039,c_7322])).

tff(c_7434,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_5042,c_7428])).

tff(c_7442,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_84,c_7434])).

tff(c_7158,plain,(
    ! [A_651,B_652] :
      ( v1_funct_1(k2_funct_2(A_651,B_652))
      | ~ m1_subset_1(B_652,k1_zfmisc_1(k2_zfmisc_1(A_651,A_651)))
      | ~ v3_funct_2(B_652,A_651,A_651)
      | ~ v1_funct_2(B_652,A_651,A_651)
      | ~ v1_funct_1(B_652) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_7356,plain,(
    ! [B_667] :
      ( v1_funct_1(k2_funct_2('#skF_1',B_667))
      | ~ m1_subset_1(B_667,k1_zfmisc_1('#skF_2'))
      | ~ v3_funct_2(B_667,'#skF_1','#skF_1')
      | ~ v1_funct_2(B_667,'#skF_1','#skF_1')
      | ~ v1_funct_1(B_667) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5039,c_7158])).

tff(c_7362,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_5042,c_7356])).

tff(c_7370,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_84,c_7362])).

tff(c_7444,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7442,c_7370])).

tff(c_7412,plain,(
    ! [A_673,B_674] :
      ( v1_funct_2(k2_funct_2(A_673,B_674),A_673,A_673)
      | ~ m1_subset_1(B_674,k1_zfmisc_1(k2_zfmisc_1(A_673,A_673)))
      | ~ v3_funct_2(B_674,A_673,A_673)
      | ~ v1_funct_2(B_674,A_673,A_673)
      | ~ v1_funct_1(B_674) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_7557,plain,(
    ! [B_684] :
      ( v1_funct_2(k2_funct_2('#skF_1',B_684),'#skF_1','#skF_1')
      | ~ m1_subset_1(B_684,k1_zfmisc_1('#skF_2'))
      | ~ v3_funct_2(B_684,'#skF_1','#skF_1')
      | ~ v1_funct_2(B_684,'#skF_1','#skF_1')
      | ~ v1_funct_1(B_684) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5039,c_7412])).

tff(c_7563,plain,
    ( v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_7442,c_7557])).

tff(c_7566,plain,(
    v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_84,c_5042,c_7563])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6865,plain,(
    ! [A_6] :
      ( k1_relset_1('#skF_1','#skF_1',A_6) = '#skF_1'
      | ~ v1_funct_2(A_6,'#skF_1','#skF_1')
      | ~ r1_tarski(A_6,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_18,c_6849])).

tff(c_7570,plain,
    ( k1_relset_1('#skF_1','#skF_1',k2_funct_1('#skF_2')) = '#skF_1'
    | ~ r1_tarski(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_7566,c_6865])).

tff(c_7571,plain,(
    ~ r1_tarski(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_7570])).

tff(c_7602,plain,(
    ! [A_686,B_687] :
      ( m1_subset_1(k2_funct_2(A_686,B_687),k1_zfmisc_1(k2_zfmisc_1(A_686,A_686)))
      | ~ m1_subset_1(B_687,k1_zfmisc_1(k2_zfmisc_1(A_686,A_686)))
      | ~ v3_funct_2(B_687,A_686,A_686)
      | ~ v1_funct_2(B_687,A_686,A_686)
      | ~ v1_funct_1(B_687) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_7644,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_7442,c_7602])).

tff(c_7671,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_84,c_5042,c_5039,c_5039,c_7644])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_7709,plain,(
    r1_tarski(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_7671,c_16])).

tff(c_7735,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7571,c_7709])).

tff(c_7737,plain,(
    r1_tarski(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_7570])).

tff(c_7992,plain,(
    ! [A_691,F_694,D_695,B_696,C_693,E_692] :
      ( k1_partfun1(A_691,B_696,C_693,D_695,E_692,F_694) = k5_relat_1(E_692,F_694)
      | ~ m1_subset_1(F_694,k1_zfmisc_1(k2_zfmisc_1(C_693,D_695)))
      | ~ v1_funct_1(F_694)
      | ~ m1_subset_1(E_692,k1_zfmisc_1(k2_zfmisc_1(A_691,B_696)))
      | ~ v1_funct_1(E_692) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_9645,plain,(
    ! [E_764,A_762,D_763,A_759,B_760,C_761] :
      ( k1_partfun1(A_759,B_760,C_761,D_763,E_764,A_762) = k5_relat_1(E_764,A_762)
      | ~ v1_funct_1(A_762)
      | ~ m1_subset_1(E_764,k1_zfmisc_1(k2_zfmisc_1(A_759,B_760)))
      | ~ v1_funct_1(E_764)
      | ~ r1_tarski(A_762,k2_zfmisc_1(C_761,D_763)) ) ),
    inference(resolution,[status(thm)],[c_18,c_7992])).

tff(c_9667,plain,(
    ! [C_765,D_766,E_767,A_768] :
      ( k1_partfun1('#skF_1','#skF_1',C_765,D_766,E_767,A_768) = k5_relat_1(E_767,A_768)
      | ~ v1_funct_1(A_768)
      | ~ m1_subset_1(E_767,k1_zfmisc_1('#skF_2'))
      | ~ v1_funct_1(E_767)
      | ~ r1_tarski(A_768,k2_zfmisc_1(C_765,D_766)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5039,c_9645])).

tff(c_9681,plain,(
    ! [C_765,D_766,A_768] :
      ( k1_partfun1('#skF_1','#skF_1',C_765,D_766,'#skF_2',A_768) = k5_relat_1('#skF_2',A_768)
      | ~ v1_funct_1(A_768)
      | ~ v1_funct_1('#skF_2')
      | ~ r1_tarski(A_768,k2_zfmisc_1(C_765,D_766)) ) ),
    inference(resolution,[status(thm)],[c_5042,c_9667])).

tff(c_9705,plain,(
    ! [C_769,D_770,A_771] :
      ( k1_partfun1('#skF_1','#skF_1',C_769,D_770,'#skF_2',A_771) = k5_relat_1('#skF_2',A_771)
      | ~ v1_funct_1(A_771)
      | ~ r1_tarski(A_771,k2_zfmisc_1(C_769,D_770)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_9681])).

tff(c_9733,plain,(
    ! [A_772] :
      ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',A_772) = k5_relat_1('#skF_2',A_772)
      | ~ v1_funct_1(A_772)
      | ~ r1_tarski(A_772,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5039,c_9705])).

tff(c_9748,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_7737,c_9733])).

tff(c_9774,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7444,c_9748])).

tff(c_7445,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7442,c_166])).

tff(c_9780,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9774,c_7445])).

tff(c_9787,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k1_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_9780])).

tff(c_9790,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_245,c_88,c_6367,c_5269,c_6864,c_9787])).

tff(c_9792,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_5052])).

tff(c_9791,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_5052])).

tff(c_9891,plain,
    ( '#skF_2' = '#skF_1'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9792,c_9792,c_9791])).

tff(c_9892,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_9891])).

tff(c_9805,plain,(
    ! [A_3] : r1_tarski('#skF_2',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9792,c_8])).

tff(c_9899,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9892,c_9805])).

tff(c_9979,plain,(
    ! [A_781,B_782,D_783] :
      ( r2_relset_1(A_781,B_782,D_783,D_783)
      | ~ m1_subset_1(D_783,k1_zfmisc_1(k2_zfmisc_1(A_781,B_782))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_10518,plain,(
    ! [A_858,B_859,A_860] :
      ( r2_relset_1(A_858,B_859,A_860,A_860)
      | ~ r1_tarski(A_860,k2_zfmisc_1(A_858,B_859)) ) ),
    inference(resolution,[status(thm)],[c_18,c_9979])).

tff(c_10531,plain,(
    ! [A_858,B_859] : r2_relset_1(A_858,B_859,'#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_9899,c_10518])).

tff(c_9915,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9892,c_88])).

tff(c_9912,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9892,c_245])).

tff(c_148,plain,(
    ! [A_52] : m1_subset_1(k6_partfun1(A_52),k1_zfmisc_1(k2_zfmisc_1(A_52,A_52))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_155,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_148])).

tff(c_164,plain,(
    r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_155,c_16])).

tff(c_193,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k6_partfun1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_164,c_189])).

tff(c_203,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_193])).

tff(c_9801,plain,(
    k6_partfun1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9792,c_9792,c_203])).

tff(c_9903,plain,(
    k6_partfun1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9892,c_9892,c_9801])).

tff(c_9913,plain,(
    v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9892,c_84])).

tff(c_10421,plain,(
    ! [C_836,A_837,B_838] :
      ( v2_funct_1(C_836)
      | ~ v3_funct_2(C_836,A_837,B_838)
      | ~ v1_funct_1(C_836)
      | ~ m1_subset_1(C_836,k1_zfmisc_1(k2_zfmisc_1(A_837,B_838))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_10755,plain,(
    ! [A_894] :
      ( v2_funct_1(k6_partfun1(A_894))
      | ~ v3_funct_2(k6_partfun1(A_894),A_894,A_894)
      | ~ v1_funct_1(k6_partfun1(A_894)) ) ),
    inference(resolution,[status(thm)],[c_72,c_10421])).

tff(c_10758,plain,
    ( v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1(k6_partfun1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_9903,c_10755])).

tff(c_10760,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9915,c_9903,c_9913,c_9903,c_10758])).

tff(c_20,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_9806,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9792,c_9792,c_20])).

tff(c_9901,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9892,c_9892,c_9806])).

tff(c_22,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_9807,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9792,c_9792,c_22])).

tff(c_9902,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9892,c_9892,c_9807])).

tff(c_9908,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9892,c_9892,c_5042])).

tff(c_9804,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_2',B_5) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9792,c_9792,c_14])).

tff(c_9991,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9892,c_9892,c_9804])).

tff(c_10100,plain,(
    ! [A_790,B_791,C_792] :
      ( k1_relset_1(A_790,B_791,C_792) = k1_relat_1(C_792)
      | ~ m1_subset_1(C_792,k1_zfmisc_1(k2_zfmisc_1(A_790,B_791))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_10584,plain,(
    ! [B_870,C_871] :
      ( k1_relset_1('#skF_1',B_870,C_871) = k1_relat_1(C_871)
      | ~ m1_subset_1(C_871,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9991,c_10100])).

tff(c_10586,plain,(
    ! [B_870] : k1_relset_1('#skF_1',B_870,'#skF_1') = k1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_9908,c_10584])).

tff(c_10591,plain,(
    ! [B_870] : k1_relset_1('#skF_1',B_870,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9902,c_10586])).

tff(c_9905,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9892,c_9792])).

tff(c_50,plain,(
    ! [C_27,B_26] :
      ( v1_funct_2(C_27,k1_xboole_0,B_26)
      | k1_relset_1(k1_xboole_0,B_26,C_27) != k1_xboole_0
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_91,plain,(
    ! [C_27,B_26] :
      ( v1_funct_2(C_27,k1_xboole_0,B_26)
      | k1_relset_1(k1_xboole_0,B_26,C_27) != k1_xboole_0
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_50])).

tff(c_10196,plain,(
    ! [C_802,B_803] :
      ( v1_funct_2(C_802,'#skF_1',B_803)
      | k1_relset_1('#skF_1',B_803,C_802) != '#skF_1'
      | ~ m1_subset_1(C_802,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9905,c_9905,c_9905,c_9905,c_91])).

tff(c_10202,plain,(
    ! [B_803] :
      ( v1_funct_2('#skF_1','#skF_1',B_803)
      | k1_relset_1('#skF_1',B_803,'#skF_1') != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_9908,c_10196])).

tff(c_10595,plain,(
    ! [B_803] : v1_funct_2('#skF_1','#skF_1',B_803) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10591,c_10202])).

tff(c_10761,plain,(
    ! [A_895,B_896] :
      ( k2_funct_2(A_895,B_896) = k2_funct_1(B_896)
      | ~ m1_subset_1(B_896,k1_zfmisc_1(k2_zfmisc_1(A_895,A_895)))
      | ~ v3_funct_2(B_896,A_895,A_895)
      | ~ v1_funct_2(B_896,A_895,A_895)
      | ~ v1_funct_1(B_896) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_11318,plain,(
    ! [B_967] :
      ( k2_funct_2('#skF_1',B_967) = k2_funct_1(B_967)
      | ~ m1_subset_1(B_967,k1_zfmisc_1('#skF_1'))
      | ~ v3_funct_2(B_967,'#skF_1','#skF_1')
      | ~ v1_funct_2(B_967,'#skF_1','#skF_1')
      | ~ v1_funct_1(B_967) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9991,c_10761])).

tff(c_11321,plain,
    ( k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1')
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_9908,c_11318])).

tff(c_11328,plain,(
    k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9915,c_10595,c_9913,c_11321])).

tff(c_11338,plain,
    ( m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_11328,c_62])).

tff(c_11344,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9915,c_10595,c_9913,c_9908,c_9991,c_9991,c_11338])).

tff(c_11409,plain,(
    r1_tarski(k2_funct_1('#skF_1'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_11344,c_16])).

tff(c_209,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_189])).

tff(c_9797,plain,(
    ! [A_3] :
      ( A_3 = '#skF_2'
      | ~ r1_tarski(A_3,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9792,c_9792,c_209])).

tff(c_10071,plain,(
    ! [A_3] :
      ( A_3 = '#skF_1'
      | ~ r1_tarski(A_3,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9892,c_9892,c_9797])).

tff(c_11426,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_11409,c_10071])).

tff(c_11446,plain,
    ( k6_partfun1(k2_relat_1('#skF_1')) = k5_relat_1('#skF_1','#skF_1')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_11426,c_90])).

tff(c_11452,plain,(
    k5_relat_1('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9912,c_9915,c_10760,c_9903,c_9901,c_11446])).

tff(c_11052,plain,(
    ! [F_936,E_934,C_935,A_933,D_937,B_938] :
      ( k1_partfun1(A_933,B_938,C_935,D_937,E_934,F_936) = k5_relat_1(E_934,F_936)
      | ~ m1_subset_1(F_936,k1_zfmisc_1(k2_zfmisc_1(C_935,D_937)))
      | ~ v1_funct_1(F_936)
      | ~ m1_subset_1(E_934,k1_zfmisc_1(k2_zfmisc_1(A_933,B_938)))
      | ~ v1_funct_1(E_934) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_12116,plain,(
    ! [A_1012,B_1013,A_1014,E_1015] :
      ( k1_partfun1(A_1012,B_1013,A_1014,A_1014,E_1015,k6_partfun1(A_1014)) = k5_relat_1(E_1015,k6_partfun1(A_1014))
      | ~ v1_funct_1(k6_partfun1(A_1014))
      | ~ m1_subset_1(E_1015,k1_zfmisc_1(k2_zfmisc_1(A_1012,B_1013)))
      | ~ v1_funct_1(E_1015) ) ),
    inference(resolution,[status(thm)],[c_72,c_11052])).

tff(c_12118,plain,(
    ! [A_1012,B_1013,E_1015] :
      ( k1_partfun1(A_1012,B_1013,'#skF_1','#skF_1',E_1015,k6_partfun1('#skF_1')) = k5_relat_1(E_1015,k6_partfun1('#skF_1'))
      | ~ v1_funct_1('#skF_1')
      | ~ m1_subset_1(E_1015,k1_zfmisc_1(k2_zfmisc_1(A_1012,B_1013)))
      | ~ v1_funct_1(E_1015) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9903,c_12116])).

tff(c_12121,plain,(
    ! [A_1016,B_1017,E_1018] :
      ( k1_partfun1(A_1016,B_1017,'#skF_1','#skF_1',E_1018,'#skF_1') = k5_relat_1(E_1018,'#skF_1')
      | ~ m1_subset_1(E_1018,k1_zfmisc_1(k2_zfmisc_1(A_1016,B_1017)))
      | ~ v1_funct_1(E_1018) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9915,c_9903,c_9903,c_12118])).

tff(c_12141,plain,(
    ! [A_1019] :
      ( k1_partfun1(A_1019,A_1019,'#skF_1','#skF_1',k6_partfun1(A_1019),'#skF_1') = k5_relat_1(k6_partfun1(A_1019),'#skF_1')
      | ~ v1_funct_1(k6_partfun1(A_1019)) ) ),
    inference(resolution,[status(thm)],[c_72,c_12121])).

tff(c_12143,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k6_partfun1('#skF_1'),'#skF_1') = k5_relat_1(k6_partfun1('#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_9903,c_12141])).

tff(c_12145,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9915,c_11452,c_9903,c_9903,c_12143])).

tff(c_9911,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9892,c_9892,c_166])).

tff(c_10068,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9903,c_9911])).

tff(c_11331,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_1')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11328,c_10068])).

tff(c_11432,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11426,c_11331])).

tff(c_12146,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12145,c_11432])).

tff(c_12149,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10531,c_12146])).

tff(c_12150,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_9891])).

tff(c_12151,plain,(
    '#skF_2' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_9891])).

tff(c_12187,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12150,c_12151])).

tff(c_12188,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_13453,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13451,c_12188])).

tff(c_14517,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1(k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14473,c_13453])).

tff(c_14524,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k2_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_14517])).

tff(c_14527,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12274,c_88,c_12864,c_12492,c_12747,c_14524])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:41:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.08/4.01  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.19/4.04  
% 10.19/4.04  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.19/4.04  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 10.19/4.04  
% 10.19/4.04  %Foreground sorts:
% 10.19/4.04  
% 10.19/4.04  
% 10.19/4.04  %Background operators:
% 10.19/4.04  
% 10.19/4.04  
% 10.19/4.04  %Foreground operators:
% 10.19/4.04  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.19/4.04  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 10.19/4.04  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 10.19/4.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.19/4.04  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 10.19/4.04  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.19/4.04  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 10.19/4.04  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 10.19/4.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.19/4.04  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.19/4.04  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.19/4.04  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.19/4.04  tff('#skF_2', type, '#skF_2': $i).
% 10.19/4.04  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 10.19/4.04  tff('#skF_1', type, '#skF_1': $i).
% 10.19/4.04  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 10.19/4.04  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 10.19/4.04  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 10.19/4.04  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.19/4.04  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 10.19/4.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.19/4.04  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.19/4.04  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.19/4.04  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 10.19/4.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.19/4.04  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 10.19/4.04  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 10.19/4.04  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.19/4.04  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.19/4.04  
% 10.19/4.08  tff(f_171, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_funct_2)).
% 10.19/4.08  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 10.19/4.08  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 10.19/4.08  tff(f_136, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 10.19/4.08  tff(f_78, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 10.19/4.08  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 10.19/4.08  tff(f_116, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 10.19/4.08  tff(f_158, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 10.19/4.08  tff(f_56, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 10.19/4.08  tff(f_156, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 10.19/4.08  tff(f_132, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 10.19/4.08  tff(f_146, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 10.19/4.08  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 10.19/4.08  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 10.19/4.08  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 10.19/4.08  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 10.19/4.08  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 10.19/4.08  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.19/4.08  tff(f_46, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 10.19/4.08  tff(c_82, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_171])).
% 10.19/4.08  tff(c_12257, plain, (![C_1027, A_1028, B_1029]: (v1_relat_1(C_1027) | ~m1_subset_1(C_1027, k1_zfmisc_1(k2_zfmisc_1(A_1028, B_1029))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 10.19/4.08  tff(c_12274, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_82, c_12257])).
% 10.19/4.08  tff(c_88, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_171])).
% 10.19/4.08  tff(c_84, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_171])).
% 10.19/4.08  tff(c_12843, plain, (![C_1115, A_1116, B_1117]: (v2_funct_1(C_1115) | ~v3_funct_2(C_1115, A_1116, B_1117) | ~v1_funct_1(C_1115) | ~m1_subset_1(C_1115, k1_zfmisc_1(k2_zfmisc_1(A_1116, B_1117))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 10.19/4.08  tff(c_12856, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_82, c_12843])).
% 10.19/4.08  tff(c_12864, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_84, c_12856])).
% 10.19/4.08  tff(c_72, plain, (![A_32]: (m1_subset_1(k6_partfun1(A_32), k1_zfmisc_1(k2_zfmisc_1(A_32, A_32))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 10.19/4.08  tff(c_12480, plain, (![A_1064, B_1065, D_1066]: (r2_relset_1(A_1064, B_1065, D_1066, D_1066) | ~m1_subset_1(D_1066, k1_zfmisc_1(k2_zfmisc_1(A_1064, B_1065))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.19/4.08  tff(c_12492, plain, (![A_32]: (r2_relset_1(A_32, A_32, k6_partfun1(A_32), k6_partfun1(A_32)))), inference(resolution, [status(thm)], [c_72, c_12480])).
% 10.19/4.08  tff(c_12384, plain, (![C_1048, B_1049, A_1050]: (v5_relat_1(C_1048, B_1049) | ~m1_subset_1(C_1048, k1_zfmisc_1(k2_zfmisc_1(A_1050, B_1049))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 10.19/4.08  tff(c_12403, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_82, c_12384])).
% 10.19/4.08  tff(c_12514, plain, (![B_1070, A_1071]: (k2_relat_1(B_1070)=A_1071 | ~v2_funct_2(B_1070, A_1071) | ~v5_relat_1(B_1070, A_1071) | ~v1_relat_1(B_1070))), inference(cnfTransformation, [status(thm)], [f_116])).
% 10.19/4.08  tff(c_12526, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_12403, c_12514])).
% 10.19/4.08  tff(c_12536, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12274, c_12526])).
% 10.19/4.08  tff(c_12543, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_12536])).
% 10.19/4.08  tff(c_12723, plain, (![C_1103, B_1104, A_1105]: (v2_funct_2(C_1103, B_1104) | ~v3_funct_2(C_1103, A_1105, B_1104) | ~v1_funct_1(C_1103) | ~m1_subset_1(C_1103, k1_zfmisc_1(k2_zfmisc_1(A_1105, B_1104))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 10.19/4.08  tff(c_12736, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_82, c_12723])).
% 10.19/4.08  tff(c_12744, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_84, c_12736])).
% 10.19/4.08  tff(c_12746, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12543, c_12744])).
% 10.19/4.08  tff(c_12747, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_12536])).
% 10.19/4.08  tff(c_78, plain, (![A_41]: (k6_relat_1(A_41)=k6_partfun1(A_41))), inference(cnfTransformation, [status(thm)], [f_158])).
% 10.19/4.08  tff(c_24, plain, (![A_8]: (k5_relat_1(k2_funct_1(A_8), A_8)=k6_relat_1(k2_relat_1(A_8)) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.19/4.08  tff(c_90, plain, (![A_8]: (k5_relat_1(k2_funct_1(A_8), A_8)=k6_partfun1(k2_relat_1(A_8)) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_24])).
% 10.19/4.08  tff(c_86, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_171])).
% 10.19/4.08  tff(c_13428, plain, (![A_1207, B_1208]: (k2_funct_2(A_1207, B_1208)=k2_funct_1(B_1208) | ~m1_subset_1(B_1208, k1_zfmisc_1(k2_zfmisc_1(A_1207, A_1207))) | ~v3_funct_2(B_1208, A_1207, A_1207) | ~v1_funct_2(B_1208, A_1207, A_1207) | ~v1_funct_1(B_1208))), inference(cnfTransformation, [status(thm)], [f_156])).
% 10.19/4.08  tff(c_13442, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_82, c_13428])).
% 10.19/4.08  tff(c_13451, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_84, c_13442])).
% 10.19/4.08  tff(c_13329, plain, (![A_1189, B_1190]: (v1_funct_1(k2_funct_2(A_1189, B_1190)) | ~m1_subset_1(B_1190, k1_zfmisc_1(k2_zfmisc_1(A_1189, A_1189))) | ~v3_funct_2(B_1190, A_1189, A_1189) | ~v1_funct_2(B_1190, A_1189, A_1189) | ~v1_funct_1(B_1190))), inference(cnfTransformation, [status(thm)], [f_132])).
% 10.19/4.08  tff(c_13343, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_82, c_13329])).
% 10.19/4.08  tff(c_13352, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_84, c_13343])).
% 10.19/4.08  tff(c_13452, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_13451, c_13352])).
% 10.19/4.08  tff(c_62, plain, (![A_30, B_31]: (m1_subset_1(k2_funct_2(A_30, B_31), k1_zfmisc_1(k2_zfmisc_1(A_30, A_30))) | ~m1_subset_1(B_31, k1_zfmisc_1(k2_zfmisc_1(A_30, A_30))) | ~v3_funct_2(B_31, A_30, A_30) | ~v1_funct_2(B_31, A_30, A_30) | ~v1_funct_1(B_31))), inference(cnfTransformation, [status(thm)], [f_132])).
% 10.19/4.08  tff(c_13827, plain, (![C_1239, B_1242, D_1241, F_1240, E_1238, A_1237]: (k1_partfun1(A_1237, B_1242, C_1239, D_1241, E_1238, F_1240)=k5_relat_1(E_1238, F_1240) | ~m1_subset_1(F_1240, k1_zfmisc_1(k2_zfmisc_1(C_1239, D_1241))) | ~v1_funct_1(F_1240) | ~m1_subset_1(E_1238, k1_zfmisc_1(k2_zfmisc_1(A_1237, B_1242))) | ~v1_funct_1(E_1238))), inference(cnfTransformation, [status(thm)], [f_146])).
% 10.19/4.08  tff(c_13840, plain, (![A_1237, B_1242, E_1238]: (k1_partfun1(A_1237, B_1242, '#skF_1', '#skF_1', E_1238, '#skF_2')=k5_relat_1(E_1238, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_1238, k1_zfmisc_1(k2_zfmisc_1(A_1237, B_1242))) | ~v1_funct_1(E_1238))), inference(resolution, [status(thm)], [c_82, c_13827])).
% 10.19/4.08  tff(c_13866, plain, (![A_1243, B_1244, E_1245]: (k1_partfun1(A_1243, B_1244, '#skF_1', '#skF_1', E_1245, '#skF_2')=k5_relat_1(E_1245, '#skF_2') | ~m1_subset_1(E_1245, k1_zfmisc_1(k2_zfmisc_1(A_1243, B_1244))) | ~v1_funct_1(E_1245))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_13840])).
% 10.19/4.08  tff(c_14437, plain, (![A_1259, B_1260]: (k1_partfun1(A_1259, A_1259, '#skF_1', '#skF_1', k2_funct_2(A_1259, B_1260), '#skF_2')=k5_relat_1(k2_funct_2(A_1259, B_1260), '#skF_2') | ~v1_funct_1(k2_funct_2(A_1259, B_1260)) | ~m1_subset_1(B_1260, k1_zfmisc_1(k2_zfmisc_1(A_1259, A_1259))) | ~v3_funct_2(B_1260, A_1259, A_1259) | ~v1_funct_2(B_1260, A_1259, A_1259) | ~v1_funct_1(B_1260))), inference(resolution, [status(thm)], [c_62, c_13866])).
% 10.19/4.08  tff(c_14455, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2')=k5_relat_1(k2_funct_2('#skF_1', '#skF_2'), '#skF_2') | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_82, c_14437])).
% 10.19/4.08  tff(c_14473, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2')=k5_relat_1(k2_funct_1('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_84, c_13452, c_13451, c_13451, c_13451, c_14455])).
% 10.19/4.08  tff(c_228, plain, (![C_58, A_59, B_60]: (v1_relat_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 10.19/4.08  tff(c_245, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_82, c_228])).
% 10.19/4.08  tff(c_873, plain, (![C_157, A_158, B_159]: (v2_funct_1(C_157) | ~v3_funct_2(C_157, A_158, B_159) | ~v1_funct_1(C_157) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_158, B_159))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 10.19/4.08  tff(c_886, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_82, c_873])).
% 10.19/4.08  tff(c_894, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_84, c_886])).
% 10.19/4.08  tff(c_749, plain, (![A_139, B_140, D_141]: (r2_relset_1(A_139, B_140, D_141, D_141) | ~m1_subset_1(D_141, k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.19/4.08  tff(c_761, plain, (![A_32]: (r2_relset_1(A_32, A_32, k6_partfun1(A_32), k6_partfun1(A_32)))), inference(resolution, [status(thm)], [c_72, c_749])).
% 10.19/4.08  tff(c_773, plain, (![A_143, B_144, C_145]: (k1_relset_1(A_143, B_144, C_145)=k1_relat_1(C_145) | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1(A_143, B_144))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.19/4.08  tff(c_792, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_82, c_773])).
% 10.19/4.08  tff(c_1070, plain, (![B_191, A_192, C_193]: (k1_xboole_0=B_191 | k1_relset_1(A_192, B_191, C_193)=A_192 | ~v1_funct_2(C_193, A_192, B_191) | ~m1_subset_1(C_193, k1_zfmisc_1(k2_zfmisc_1(A_192, B_191))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 10.19/4.08  tff(c_1083, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_82, c_1070])).
% 10.19/4.08  tff(c_1093, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_792, c_1083])).
% 10.19/4.08  tff(c_1094, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_1093])).
% 10.19/4.08  tff(c_26, plain, (![A_8]: (k5_relat_1(A_8, k2_funct_1(A_8))=k6_relat_1(k1_relat_1(A_8)) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.19/4.08  tff(c_89, plain, (![A_8]: (k5_relat_1(A_8, k2_funct_1(A_8))=k6_partfun1(k1_relat_1(A_8)) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_26])).
% 10.19/4.08  tff(c_1403, plain, (![A_239, B_240]: (k2_funct_2(A_239, B_240)=k2_funct_1(B_240) | ~m1_subset_1(B_240, k1_zfmisc_1(k2_zfmisc_1(A_239, A_239))) | ~v3_funct_2(B_240, A_239, A_239) | ~v1_funct_2(B_240, A_239, A_239) | ~v1_funct_1(B_240))), inference(cnfTransformation, [status(thm)], [f_156])).
% 10.19/4.08  tff(c_1417, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_82, c_1403])).
% 10.19/4.08  tff(c_1426, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_84, c_1417])).
% 10.19/4.08  tff(c_1377, plain, (![A_233, B_234]: (v1_funct_1(k2_funct_2(A_233, B_234)) | ~m1_subset_1(B_234, k1_zfmisc_1(k2_zfmisc_1(A_233, A_233))) | ~v3_funct_2(B_234, A_233, A_233) | ~v1_funct_2(B_234, A_233, A_233) | ~v1_funct_1(B_234))), inference(cnfTransformation, [status(thm)], [f_132])).
% 10.19/4.08  tff(c_1391, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_82, c_1377])).
% 10.19/4.08  tff(c_1400, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_84, c_1391])).
% 10.19/4.08  tff(c_1427, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1426, c_1400])).
% 10.19/4.08  tff(c_1519, plain, (![A_258, B_259]: (m1_subset_1(k2_funct_2(A_258, B_259), k1_zfmisc_1(k2_zfmisc_1(A_258, A_258))) | ~m1_subset_1(B_259, k1_zfmisc_1(k2_zfmisc_1(A_258, A_258))) | ~v3_funct_2(B_259, A_258, A_258) | ~v1_funct_2(B_259, A_258, A_258) | ~v1_funct_1(B_259))), inference(cnfTransformation, [status(thm)], [f_132])).
% 10.19/4.08  tff(c_1561, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1426, c_1519])).
% 10.19/4.08  tff(c_1585, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_84, c_82, c_1561])).
% 10.19/4.08  tff(c_1715, plain, (![D_264, A_260, B_265, E_261, F_263, C_262]: (k1_partfun1(A_260, B_265, C_262, D_264, E_261, F_263)=k5_relat_1(E_261, F_263) | ~m1_subset_1(F_263, k1_zfmisc_1(k2_zfmisc_1(C_262, D_264))) | ~v1_funct_1(F_263) | ~m1_subset_1(E_261, k1_zfmisc_1(k2_zfmisc_1(A_260, B_265))) | ~v1_funct_1(E_261))), inference(cnfTransformation, [status(thm)], [f_146])).
% 10.19/4.08  tff(c_1717, plain, (![A_260, B_265, E_261]: (k1_partfun1(A_260, B_265, '#skF_1', '#skF_1', E_261, k2_funct_1('#skF_2'))=k5_relat_1(E_261, k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~m1_subset_1(E_261, k1_zfmisc_1(k2_zfmisc_1(A_260, B_265))) | ~v1_funct_1(E_261))), inference(resolution, [status(thm)], [c_1585, c_1715])).
% 10.19/4.08  tff(c_4778, plain, (![A_368, B_369, E_370]: (k1_partfun1(A_368, B_369, '#skF_1', '#skF_1', E_370, k2_funct_1('#skF_2'))=k5_relat_1(E_370, k2_funct_1('#skF_2')) | ~m1_subset_1(E_370, k1_zfmisc_1(k2_zfmisc_1(A_368, B_369))) | ~v1_funct_1(E_370))), inference(demodulation, [status(thm), theory('equality')], [c_1427, c_1717])).
% 10.19/4.08  tff(c_4818, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2')) | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_82, c_4778])).
% 10.19/4.08  tff(c_4851, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_4818])).
% 10.19/4.08  tff(c_80, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1')) | ~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_171])).
% 10.19/4.08  tff(c_166, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(splitLeft, [status(thm)], [c_80])).
% 10.19/4.08  tff(c_1428, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1426, c_166])).
% 10.19/4.08  tff(c_4852, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4851, c_1428])).
% 10.19/4.08  tff(c_4859, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k1_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_89, c_4852])).
% 10.19/4.08  tff(c_4862, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_245, c_88, c_894, c_761, c_1094, c_4859])).
% 10.19/4.08  tff(c_4863, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_1093])).
% 10.19/4.08  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.19/4.08  tff(c_4898, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_4863, c_8])).
% 10.19/4.08  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.19/4.08  tff(c_4897, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4863, c_4863, c_14])).
% 10.19/4.08  tff(c_139, plain, (![A_50, B_51]: (r1_tarski(A_50, B_51) | ~m1_subset_1(A_50, k1_zfmisc_1(B_51)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.19/4.08  tff(c_147, plain, (r1_tarski('#skF_2', k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_82, c_139])).
% 10.19/4.08  tff(c_189, plain, (![B_56, A_57]: (B_56=A_57 | ~r1_tarski(B_56, A_57) | ~r1_tarski(A_57, B_56))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.19/4.08  tff(c_204, plain, (k2_zfmisc_1('#skF_1', '#skF_1')='#skF_2' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_147, c_189])).
% 10.19/4.08  tff(c_316, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_2')), inference(splitLeft, [status(thm)], [c_204])).
% 10.19/4.08  tff(c_5033, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4897, c_316])).
% 10.19/4.08  tff(c_5038, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4898, c_5033])).
% 10.19/4.08  tff(c_5039, plain, (k2_zfmisc_1('#skF_1', '#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_204])).
% 10.19/4.08  tff(c_5042, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_5039, c_82])).
% 10.19/4.08  tff(c_6238, plain, (![C_558, A_559, B_560]: (v2_funct_1(C_558) | ~v3_funct_2(C_558, A_559, B_560) | ~v1_funct_1(C_558) | ~m1_subset_1(C_558, k1_zfmisc_1(k2_zfmisc_1(A_559, B_560))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 10.19/4.08  tff(c_6353, plain, (![C_574]: (v2_funct_1(C_574) | ~v3_funct_2(C_574, '#skF_1', '#skF_1') | ~v1_funct_1(C_574) | ~m1_subset_1(C_574, k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_5039, c_6238])).
% 10.19/4.08  tff(c_6359, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_5042, c_6353])).
% 10.19/4.08  tff(c_6367, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_84, c_6359])).
% 10.19/4.08  tff(c_5257, plain, (![A_410, B_411, D_412]: (r2_relset_1(A_410, B_411, D_412, D_412) | ~m1_subset_1(D_412, k1_zfmisc_1(k2_zfmisc_1(A_410, B_411))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.19/4.08  tff(c_5269, plain, (![A_32]: (r2_relset_1(A_32, A_32, k6_partfun1(A_32), k6_partfun1(A_32)))), inference(resolution, [status(thm)], [c_72, c_5257])).
% 10.19/4.08  tff(c_6089, plain, (![A_541, B_542, C_543]: (k1_relset_1(A_541, B_542, C_543)=k1_relat_1(C_543) | ~m1_subset_1(C_543, k1_zfmisc_1(k2_zfmisc_1(A_541, B_542))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.19/4.08  tff(c_6134, plain, (![C_547]: (k1_relset_1('#skF_1', '#skF_1', C_547)=k1_relat_1(C_547) | ~m1_subset_1(C_547, k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_5039, c_6089])).
% 10.19/4.08  tff(c_6147, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_5042, c_6134])).
% 10.19/4.08  tff(c_6499, plain, (![B_601, A_602, C_603]: (k1_xboole_0=B_601 | k1_relset_1(A_602, B_601, C_603)=A_602 | ~v1_funct_2(C_603, A_602, B_601) | ~m1_subset_1(C_603, k1_zfmisc_1(k2_zfmisc_1(A_602, B_601))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 10.19/4.08  tff(c_6502, plain, (![C_603]: (k1_xboole_0='#skF_1' | k1_relset_1('#skF_1', '#skF_1', C_603)='#skF_1' | ~v1_funct_2(C_603, '#skF_1', '#skF_1') | ~m1_subset_1(C_603, k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_5039, c_6499])).
% 10.19/4.08  tff(c_6552, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_6502])).
% 10.19/4.08  tff(c_10, plain, (![B_5, A_4]: (k1_xboole_0=B_5 | k1_xboole_0=A_4 | k2_zfmisc_1(A_4, B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.19/4.08  tff(c_5052, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_5039, c_10])).
% 10.19/4.08  tff(c_5099, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_5052])).
% 10.19/4.08  tff(c_6588, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6552, c_5099])).
% 10.19/4.08  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.19/4.08  tff(c_6597, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6552, c_6552, c_12])).
% 10.19/4.08  tff(c_6837, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6597, c_5039])).
% 10.19/4.08  tff(c_6839, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6588, c_6837])).
% 10.19/4.08  tff(c_6849, plain, (![C_621]: (k1_relset_1('#skF_1', '#skF_1', C_621)='#skF_1' | ~v1_funct_2(C_621, '#skF_1', '#skF_1') | ~m1_subset_1(C_621, k1_zfmisc_1('#skF_2')))), inference(splitRight, [status(thm)], [c_6502])).
% 10.19/4.08  tff(c_6855, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_5042, c_6849])).
% 10.19/4.08  tff(c_6864, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_6147, c_6855])).
% 10.19/4.08  tff(c_7322, plain, (![A_663, B_664]: (k2_funct_2(A_663, B_664)=k2_funct_1(B_664) | ~m1_subset_1(B_664, k1_zfmisc_1(k2_zfmisc_1(A_663, A_663))) | ~v3_funct_2(B_664, A_663, A_663) | ~v1_funct_2(B_664, A_663, A_663) | ~v1_funct_1(B_664))), inference(cnfTransformation, [status(thm)], [f_156])).
% 10.19/4.08  tff(c_7428, plain, (![B_675]: (k2_funct_2('#skF_1', B_675)=k2_funct_1(B_675) | ~m1_subset_1(B_675, k1_zfmisc_1('#skF_2')) | ~v3_funct_2(B_675, '#skF_1', '#skF_1') | ~v1_funct_2(B_675, '#skF_1', '#skF_1') | ~v1_funct_1(B_675))), inference(superposition, [status(thm), theory('equality')], [c_5039, c_7322])).
% 10.19/4.08  tff(c_7434, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_5042, c_7428])).
% 10.19/4.08  tff(c_7442, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_84, c_7434])).
% 10.19/4.08  tff(c_7158, plain, (![A_651, B_652]: (v1_funct_1(k2_funct_2(A_651, B_652)) | ~m1_subset_1(B_652, k1_zfmisc_1(k2_zfmisc_1(A_651, A_651))) | ~v3_funct_2(B_652, A_651, A_651) | ~v1_funct_2(B_652, A_651, A_651) | ~v1_funct_1(B_652))), inference(cnfTransformation, [status(thm)], [f_132])).
% 10.19/4.08  tff(c_7356, plain, (![B_667]: (v1_funct_1(k2_funct_2('#skF_1', B_667)) | ~m1_subset_1(B_667, k1_zfmisc_1('#skF_2')) | ~v3_funct_2(B_667, '#skF_1', '#skF_1') | ~v1_funct_2(B_667, '#skF_1', '#skF_1') | ~v1_funct_1(B_667))), inference(superposition, [status(thm), theory('equality')], [c_5039, c_7158])).
% 10.19/4.08  tff(c_7362, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_5042, c_7356])).
% 10.19/4.08  tff(c_7370, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_84, c_7362])).
% 10.19/4.08  tff(c_7444, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_7442, c_7370])).
% 10.19/4.08  tff(c_7412, plain, (![A_673, B_674]: (v1_funct_2(k2_funct_2(A_673, B_674), A_673, A_673) | ~m1_subset_1(B_674, k1_zfmisc_1(k2_zfmisc_1(A_673, A_673))) | ~v3_funct_2(B_674, A_673, A_673) | ~v1_funct_2(B_674, A_673, A_673) | ~v1_funct_1(B_674))), inference(cnfTransformation, [status(thm)], [f_132])).
% 10.19/4.08  tff(c_7557, plain, (![B_684]: (v1_funct_2(k2_funct_2('#skF_1', B_684), '#skF_1', '#skF_1') | ~m1_subset_1(B_684, k1_zfmisc_1('#skF_2')) | ~v3_funct_2(B_684, '#skF_1', '#skF_1') | ~v1_funct_2(B_684, '#skF_1', '#skF_1') | ~v1_funct_1(B_684))), inference(superposition, [status(thm), theory('equality')], [c_5039, c_7412])).
% 10.19/4.08  tff(c_7563, plain, (v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_7442, c_7557])).
% 10.19/4.08  tff(c_7566, plain, (v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_84, c_5042, c_7563])).
% 10.19/4.08  tff(c_18, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.19/4.08  tff(c_6865, plain, (![A_6]: (k1_relset_1('#skF_1', '#skF_1', A_6)='#skF_1' | ~v1_funct_2(A_6, '#skF_1', '#skF_1') | ~r1_tarski(A_6, '#skF_2'))), inference(resolution, [status(thm)], [c_18, c_6849])).
% 10.19/4.08  tff(c_7570, plain, (k1_relset_1('#skF_1', '#skF_1', k2_funct_1('#skF_2'))='#skF_1' | ~r1_tarski(k2_funct_1('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_7566, c_6865])).
% 10.19/4.08  tff(c_7571, plain, (~r1_tarski(k2_funct_1('#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_7570])).
% 10.19/4.08  tff(c_7602, plain, (![A_686, B_687]: (m1_subset_1(k2_funct_2(A_686, B_687), k1_zfmisc_1(k2_zfmisc_1(A_686, A_686))) | ~m1_subset_1(B_687, k1_zfmisc_1(k2_zfmisc_1(A_686, A_686))) | ~v3_funct_2(B_687, A_686, A_686) | ~v1_funct_2(B_687, A_686, A_686) | ~v1_funct_1(B_687))), inference(cnfTransformation, [status(thm)], [f_132])).
% 10.19/4.08  tff(c_7644, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_7442, c_7602])).
% 10.19/4.08  tff(c_7671, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_84, c_5042, c_5039, c_5039, c_7644])).
% 10.19/4.08  tff(c_16, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.19/4.08  tff(c_7709, plain, (r1_tarski(k2_funct_1('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_7671, c_16])).
% 10.19/4.08  tff(c_7735, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7571, c_7709])).
% 10.19/4.08  tff(c_7737, plain, (r1_tarski(k2_funct_1('#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_7570])).
% 10.19/4.08  tff(c_7992, plain, (![A_691, F_694, D_695, B_696, C_693, E_692]: (k1_partfun1(A_691, B_696, C_693, D_695, E_692, F_694)=k5_relat_1(E_692, F_694) | ~m1_subset_1(F_694, k1_zfmisc_1(k2_zfmisc_1(C_693, D_695))) | ~v1_funct_1(F_694) | ~m1_subset_1(E_692, k1_zfmisc_1(k2_zfmisc_1(A_691, B_696))) | ~v1_funct_1(E_692))), inference(cnfTransformation, [status(thm)], [f_146])).
% 10.19/4.08  tff(c_9645, plain, (![E_764, A_762, D_763, A_759, B_760, C_761]: (k1_partfun1(A_759, B_760, C_761, D_763, E_764, A_762)=k5_relat_1(E_764, A_762) | ~v1_funct_1(A_762) | ~m1_subset_1(E_764, k1_zfmisc_1(k2_zfmisc_1(A_759, B_760))) | ~v1_funct_1(E_764) | ~r1_tarski(A_762, k2_zfmisc_1(C_761, D_763)))), inference(resolution, [status(thm)], [c_18, c_7992])).
% 10.19/4.08  tff(c_9667, plain, (![C_765, D_766, E_767, A_768]: (k1_partfun1('#skF_1', '#skF_1', C_765, D_766, E_767, A_768)=k5_relat_1(E_767, A_768) | ~v1_funct_1(A_768) | ~m1_subset_1(E_767, k1_zfmisc_1('#skF_2')) | ~v1_funct_1(E_767) | ~r1_tarski(A_768, k2_zfmisc_1(C_765, D_766)))), inference(superposition, [status(thm), theory('equality')], [c_5039, c_9645])).
% 10.19/4.08  tff(c_9681, plain, (![C_765, D_766, A_768]: (k1_partfun1('#skF_1', '#skF_1', C_765, D_766, '#skF_2', A_768)=k5_relat_1('#skF_2', A_768) | ~v1_funct_1(A_768) | ~v1_funct_1('#skF_2') | ~r1_tarski(A_768, k2_zfmisc_1(C_765, D_766)))), inference(resolution, [status(thm)], [c_5042, c_9667])).
% 10.19/4.08  tff(c_9705, plain, (![C_769, D_770, A_771]: (k1_partfun1('#skF_1', '#skF_1', C_769, D_770, '#skF_2', A_771)=k5_relat_1('#skF_2', A_771) | ~v1_funct_1(A_771) | ~r1_tarski(A_771, k2_zfmisc_1(C_769, D_770)))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_9681])).
% 10.19/4.08  tff(c_9733, plain, (![A_772]: (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', A_772)=k5_relat_1('#skF_2', A_772) | ~v1_funct_1(A_772) | ~r1_tarski(A_772, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_5039, c_9705])).
% 10.19/4.08  tff(c_9748, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_7737, c_9733])).
% 10.19/4.08  tff(c_9774, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_7444, c_9748])).
% 10.19/4.08  tff(c_7445, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_7442, c_166])).
% 10.19/4.08  tff(c_9780, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_9774, c_7445])).
% 10.19/4.08  tff(c_9787, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k1_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_89, c_9780])).
% 10.19/4.08  tff(c_9790, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_245, c_88, c_6367, c_5269, c_6864, c_9787])).
% 10.19/4.08  tff(c_9792, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_5052])).
% 10.19/4.08  tff(c_9791, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_5052])).
% 10.19/4.08  tff(c_9891, plain, ('#skF_2'='#skF_1' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9792, c_9792, c_9791])).
% 10.19/4.08  tff(c_9892, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_9891])).
% 10.19/4.08  tff(c_9805, plain, (![A_3]: (r1_tarski('#skF_2', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_9792, c_8])).
% 10.19/4.08  tff(c_9899, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_9892, c_9805])).
% 10.19/4.08  tff(c_9979, plain, (![A_781, B_782, D_783]: (r2_relset_1(A_781, B_782, D_783, D_783) | ~m1_subset_1(D_783, k1_zfmisc_1(k2_zfmisc_1(A_781, B_782))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.19/4.08  tff(c_10518, plain, (![A_858, B_859, A_860]: (r2_relset_1(A_858, B_859, A_860, A_860) | ~r1_tarski(A_860, k2_zfmisc_1(A_858, B_859)))), inference(resolution, [status(thm)], [c_18, c_9979])).
% 10.19/4.08  tff(c_10531, plain, (![A_858, B_859]: (r2_relset_1(A_858, B_859, '#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_9899, c_10518])).
% 10.19/4.08  tff(c_9915, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9892, c_88])).
% 10.19/4.08  tff(c_9912, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9892, c_245])).
% 10.19/4.08  tff(c_148, plain, (![A_52]: (m1_subset_1(k6_partfun1(A_52), k1_zfmisc_1(k2_zfmisc_1(A_52, A_52))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 10.19/4.08  tff(c_155, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_148])).
% 10.19/4.08  tff(c_164, plain, (r1_tarski(k6_partfun1(k1_xboole_0), k1_xboole_0)), inference(resolution, [status(thm)], [c_155, c_16])).
% 10.19/4.08  tff(c_193, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k6_partfun1(k1_xboole_0))), inference(resolution, [status(thm)], [c_164, c_189])).
% 10.19/4.08  tff(c_203, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8, c_193])).
% 10.19/4.08  tff(c_9801, plain, (k6_partfun1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_9792, c_9792, c_203])).
% 10.19/4.08  tff(c_9903, plain, (k6_partfun1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9892, c_9892, c_9801])).
% 10.19/4.08  tff(c_9913, plain, (v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9892, c_84])).
% 10.19/4.08  tff(c_10421, plain, (![C_836, A_837, B_838]: (v2_funct_1(C_836) | ~v3_funct_2(C_836, A_837, B_838) | ~v1_funct_1(C_836) | ~m1_subset_1(C_836, k1_zfmisc_1(k2_zfmisc_1(A_837, B_838))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 10.19/4.08  tff(c_10755, plain, (![A_894]: (v2_funct_1(k6_partfun1(A_894)) | ~v3_funct_2(k6_partfun1(A_894), A_894, A_894) | ~v1_funct_1(k6_partfun1(A_894)))), inference(resolution, [status(thm)], [c_72, c_10421])).
% 10.19/4.08  tff(c_10758, plain, (v2_funct_1(k6_partfun1('#skF_1')) | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1(k6_partfun1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_9903, c_10755])).
% 10.19/4.08  tff(c_10760, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9915, c_9903, c_9913, c_9903, c_10758])).
% 10.19/4.08  tff(c_20, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.19/4.08  tff(c_9806, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_9792, c_9792, c_20])).
% 10.19/4.08  tff(c_9901, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9892, c_9892, c_9806])).
% 10.19/4.08  tff(c_22, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.19/4.08  tff(c_9807, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_9792, c_9792, c_22])).
% 10.19/4.08  tff(c_9902, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9892, c_9892, c_9807])).
% 10.19/4.08  tff(c_9908, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_9892, c_9892, c_5042])).
% 10.19/4.08  tff(c_9804, plain, (![B_5]: (k2_zfmisc_1('#skF_2', B_5)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_9792, c_9792, c_14])).
% 10.19/4.08  tff(c_9991, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9892, c_9892, c_9804])).
% 10.19/4.08  tff(c_10100, plain, (![A_790, B_791, C_792]: (k1_relset_1(A_790, B_791, C_792)=k1_relat_1(C_792) | ~m1_subset_1(C_792, k1_zfmisc_1(k2_zfmisc_1(A_790, B_791))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.19/4.08  tff(c_10584, plain, (![B_870, C_871]: (k1_relset_1('#skF_1', B_870, C_871)=k1_relat_1(C_871) | ~m1_subset_1(C_871, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_9991, c_10100])).
% 10.19/4.08  tff(c_10586, plain, (![B_870]: (k1_relset_1('#skF_1', B_870, '#skF_1')=k1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_9908, c_10584])).
% 10.19/4.08  tff(c_10591, plain, (![B_870]: (k1_relset_1('#skF_1', B_870, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9902, c_10586])).
% 10.19/4.08  tff(c_9905, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9892, c_9792])).
% 10.19/4.08  tff(c_50, plain, (![C_27, B_26]: (v1_funct_2(C_27, k1_xboole_0, B_26) | k1_relset_1(k1_xboole_0, B_26, C_27)!=k1_xboole_0 | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_26))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 10.19/4.08  tff(c_91, plain, (![C_27, B_26]: (v1_funct_2(C_27, k1_xboole_0, B_26) | k1_relset_1(k1_xboole_0, B_26, C_27)!=k1_xboole_0 | ~m1_subset_1(C_27, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_50])).
% 10.19/4.08  tff(c_10196, plain, (![C_802, B_803]: (v1_funct_2(C_802, '#skF_1', B_803) | k1_relset_1('#skF_1', B_803, C_802)!='#skF_1' | ~m1_subset_1(C_802, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_9905, c_9905, c_9905, c_9905, c_91])).
% 10.19/4.08  tff(c_10202, plain, (![B_803]: (v1_funct_2('#skF_1', '#skF_1', B_803) | k1_relset_1('#skF_1', B_803, '#skF_1')!='#skF_1')), inference(resolution, [status(thm)], [c_9908, c_10196])).
% 10.19/4.08  tff(c_10595, plain, (![B_803]: (v1_funct_2('#skF_1', '#skF_1', B_803))), inference(demodulation, [status(thm), theory('equality')], [c_10591, c_10202])).
% 10.19/4.08  tff(c_10761, plain, (![A_895, B_896]: (k2_funct_2(A_895, B_896)=k2_funct_1(B_896) | ~m1_subset_1(B_896, k1_zfmisc_1(k2_zfmisc_1(A_895, A_895))) | ~v3_funct_2(B_896, A_895, A_895) | ~v1_funct_2(B_896, A_895, A_895) | ~v1_funct_1(B_896))), inference(cnfTransformation, [status(thm)], [f_156])).
% 10.19/4.08  tff(c_11318, plain, (![B_967]: (k2_funct_2('#skF_1', B_967)=k2_funct_1(B_967) | ~m1_subset_1(B_967, k1_zfmisc_1('#skF_1')) | ~v3_funct_2(B_967, '#skF_1', '#skF_1') | ~v1_funct_2(B_967, '#skF_1', '#skF_1') | ~v1_funct_1(B_967))), inference(superposition, [status(thm), theory('equality')], [c_9991, c_10761])).
% 10.19/4.08  tff(c_11321, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_9908, c_11318])).
% 10.19/4.08  tff(c_11328, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9915, c_10595, c_9913, c_11321])).
% 10.19/4.08  tff(c_11338, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_11328, c_62])).
% 10.19/4.08  tff(c_11344, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_9915, c_10595, c_9913, c_9908, c_9991, c_9991, c_11338])).
% 10.19/4.08  tff(c_11409, plain, (r1_tarski(k2_funct_1('#skF_1'), '#skF_1')), inference(resolution, [status(thm)], [c_11344, c_16])).
% 10.19/4.08  tff(c_209, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_189])).
% 10.19/4.08  tff(c_9797, plain, (![A_3]: (A_3='#skF_2' | ~r1_tarski(A_3, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_9792, c_9792, c_209])).
% 10.19/4.08  tff(c_10071, plain, (![A_3]: (A_3='#skF_1' | ~r1_tarski(A_3, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_9892, c_9892, c_9797])).
% 10.19/4.08  tff(c_11426, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_11409, c_10071])).
% 10.19/4.08  tff(c_11446, plain, (k6_partfun1(k2_relat_1('#skF_1'))=k5_relat_1('#skF_1', '#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_11426, c_90])).
% 10.19/4.08  tff(c_11452, plain, (k5_relat_1('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9912, c_9915, c_10760, c_9903, c_9901, c_11446])).
% 10.19/4.08  tff(c_11052, plain, (![F_936, E_934, C_935, A_933, D_937, B_938]: (k1_partfun1(A_933, B_938, C_935, D_937, E_934, F_936)=k5_relat_1(E_934, F_936) | ~m1_subset_1(F_936, k1_zfmisc_1(k2_zfmisc_1(C_935, D_937))) | ~v1_funct_1(F_936) | ~m1_subset_1(E_934, k1_zfmisc_1(k2_zfmisc_1(A_933, B_938))) | ~v1_funct_1(E_934))), inference(cnfTransformation, [status(thm)], [f_146])).
% 10.19/4.08  tff(c_12116, plain, (![A_1012, B_1013, A_1014, E_1015]: (k1_partfun1(A_1012, B_1013, A_1014, A_1014, E_1015, k6_partfun1(A_1014))=k5_relat_1(E_1015, k6_partfun1(A_1014)) | ~v1_funct_1(k6_partfun1(A_1014)) | ~m1_subset_1(E_1015, k1_zfmisc_1(k2_zfmisc_1(A_1012, B_1013))) | ~v1_funct_1(E_1015))), inference(resolution, [status(thm)], [c_72, c_11052])).
% 10.19/4.08  tff(c_12118, plain, (![A_1012, B_1013, E_1015]: (k1_partfun1(A_1012, B_1013, '#skF_1', '#skF_1', E_1015, k6_partfun1('#skF_1'))=k5_relat_1(E_1015, k6_partfun1('#skF_1')) | ~v1_funct_1('#skF_1') | ~m1_subset_1(E_1015, k1_zfmisc_1(k2_zfmisc_1(A_1012, B_1013))) | ~v1_funct_1(E_1015))), inference(superposition, [status(thm), theory('equality')], [c_9903, c_12116])).
% 10.19/4.08  tff(c_12121, plain, (![A_1016, B_1017, E_1018]: (k1_partfun1(A_1016, B_1017, '#skF_1', '#skF_1', E_1018, '#skF_1')=k5_relat_1(E_1018, '#skF_1') | ~m1_subset_1(E_1018, k1_zfmisc_1(k2_zfmisc_1(A_1016, B_1017))) | ~v1_funct_1(E_1018))), inference(demodulation, [status(thm), theory('equality')], [c_9915, c_9903, c_9903, c_12118])).
% 10.19/4.08  tff(c_12141, plain, (![A_1019]: (k1_partfun1(A_1019, A_1019, '#skF_1', '#skF_1', k6_partfun1(A_1019), '#skF_1')=k5_relat_1(k6_partfun1(A_1019), '#skF_1') | ~v1_funct_1(k6_partfun1(A_1019)))), inference(resolution, [status(thm)], [c_72, c_12121])).
% 10.19/4.08  tff(c_12143, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k6_partfun1('#skF_1'), '#skF_1')=k5_relat_1(k6_partfun1('#skF_1'), '#skF_1') | ~v1_funct_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_9903, c_12141])).
% 10.19/4.08  tff(c_12145, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9915, c_11452, c_9903, c_9903, c_12143])).
% 10.19/4.08  tff(c_9911, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_9892, c_9892, c_166])).
% 10.19/4.08  tff(c_10068, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9903, c_9911])).
% 10.19/4.08  tff(c_11331, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_1')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_11328, c_10068])).
% 10.19/4.08  tff(c_11432, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_11426, c_11331])).
% 10.19/4.08  tff(c_12146, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12145, c_11432])).
% 10.19/4.08  tff(c_12149, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10531, c_12146])).
% 10.19/4.08  tff(c_12150, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_9891])).
% 10.19/4.08  tff(c_12151, plain, ('#skF_2'!='#skF_1'), inference(splitRight, [status(thm)], [c_9891])).
% 10.19/4.08  tff(c_12187, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12150, c_12151])).
% 10.19/4.08  tff(c_12188, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(splitRight, [status(thm)], [c_80])).
% 10.19/4.08  tff(c_13453, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_13451, c_12188])).
% 10.19/4.08  tff(c_14517, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1(k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_14473, c_13453])).
% 10.19/4.08  tff(c_14524, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k2_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_90, c_14517])).
% 10.19/4.08  tff(c_14527, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12274, c_88, c_12864, c_12492, c_12747, c_14524])).
% 10.19/4.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.19/4.08  
% 10.19/4.08  Inference rules
% 10.19/4.08  ----------------------
% 10.19/4.08  #Ref     : 0
% 10.19/4.08  #Sup     : 3026
% 10.19/4.08  #Fact    : 0
% 10.19/4.08  #Define  : 0
% 10.19/4.08  #Split   : 43
% 10.19/4.08  #Chain   : 0
% 10.19/4.08  #Close   : 0
% 10.19/4.08  
% 10.19/4.08  Ordering : KBO
% 10.19/4.08  
% 10.19/4.08  Simplification rules
% 10.19/4.08  ----------------------
% 10.19/4.08  #Subsume      : 393
% 10.19/4.08  #Demod        : 4341
% 10.19/4.08  #Tautology    : 1385
% 10.19/4.08  #SimpNegUnit  : 20
% 10.19/4.08  #BackRed      : 218
% 10.19/4.08  
% 10.19/4.08  #Partial instantiations: 0
% 10.19/4.08  #Strategies tried      : 1
% 10.19/4.08  
% 10.19/4.08  Timing (in seconds)
% 10.19/4.08  ----------------------
% 10.19/4.08  Preprocessing        : 0.45
% 10.19/4.08  Parsing              : 0.23
% 10.19/4.08  CNF conversion       : 0.03
% 10.19/4.08  Main loop            : 2.71
% 10.19/4.08  Inferencing          : 0.85
% 10.19/4.08  Reduction            : 1.07
% 10.19/4.08  Demodulation         : 0.80
% 10.19/4.08  BG Simplification    : 0.08
% 10.19/4.08  Subsumption          : 0.52
% 10.19/4.08  Abstraction          : 0.09
% 10.19/4.08  MUC search           : 0.00
% 10.19/4.08  Cooper               : 0.00
% 10.19/4.08  Total                : 3.25
% 10.19/4.08  Index Insertion      : 0.00
% 10.19/4.08  Index Deletion       : 0.00
% 10.19/4.08  Index Matching       : 0.00
% 10.19/4.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
