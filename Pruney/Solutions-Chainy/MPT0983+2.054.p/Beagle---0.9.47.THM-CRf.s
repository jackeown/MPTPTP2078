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
% DateTime   : Thu Dec  3 10:12:08 EST 2020

% Result     : Theorem 4.74s
% Output     : CNFRefutation 5.10s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 373 expanded)
%              Number of leaves         :   42 ( 146 expanded)
%              Depth                    :   11
%              Number of atoms          :  221 (1077 expanded)
%              Number of equality atoms :   43 ( 109 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_158,negated_conjecture,(
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

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_99,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_93,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_97,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_138,axiom,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_116,axiom,(
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

tff(f_81,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_216,plain,(
    ! [C_74,B_75,A_76] :
      ( v1_xboole_0(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(B_75,A_76)))
      | ~ v1_xboole_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_233,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_216])).

tff(c_237,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_233])).

tff(c_50,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_103,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_64,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_62,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_60,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_58,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_56,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_42,plain,(
    ! [A_32] : k6_relat_1(A_32) = k6_partfun1(A_32) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_14,plain,(
    ! [A_5] : v2_funct_1(k6_relat_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_65,plain,(
    ! [A_5] : v2_funct_1(k6_partfun1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_14])).

tff(c_34,plain,(
    ! [A_25,F_30,E_29,C_27,D_28,B_26] :
      ( m1_subset_1(k1_partfun1(A_25,B_26,C_27,D_28,E_29,F_30),k1_zfmisc_1(k2_zfmisc_1(A_25,D_28)))
      | ~ m1_subset_1(F_30,k1_zfmisc_1(k2_zfmisc_1(C_27,D_28)))
      | ~ v1_funct_1(F_30)
      | ~ m1_subset_1(E_29,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | ~ v1_funct_1(E_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_40,plain,(
    ! [A_31] : m1_subset_1(k6_partfun1(A_31),k1_zfmisc_1(k2_zfmisc_1(A_31,A_31))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_52,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_394,plain,(
    ! [D_90,C_91,A_92,B_93] :
      ( D_90 = C_91
      | ~ r2_relset_1(A_92,B_93,C_91,D_90)
      | ~ m1_subset_1(D_90,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93)))
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_400,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_52,c_394])).

tff(c_411,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_400])).

tff(c_414,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_411])).

tff(c_819,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_414])).

tff(c_823,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_58,c_54,c_819])).

tff(c_824,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_411])).

tff(c_1139,plain,(
    ! [C_200,B_199,D_201,A_198,E_202] :
      ( k1_xboole_0 = C_200
      | v2_funct_1(D_201)
      | ~ v2_funct_1(k1_partfun1(A_198,B_199,B_199,C_200,D_201,E_202))
      | ~ m1_subset_1(E_202,k1_zfmisc_1(k2_zfmisc_1(B_199,C_200)))
      | ~ v1_funct_2(E_202,B_199,C_200)
      | ~ v1_funct_1(E_202)
      | ~ m1_subset_1(D_201,k1_zfmisc_1(k2_zfmisc_1(A_198,B_199)))
      | ~ v1_funct_2(D_201,A_198,B_199)
      | ~ v1_funct_1(D_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1141,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_824,c_1139])).

tff(c_1143,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_58,c_56,c_54,c_65,c_1141])).

tff(c_1144,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_1143])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1173,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1144,c_2])).

tff(c_1175,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_237,c_1173])).

tff(c_1176,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_233])).

tff(c_1346,plain,(
    ! [A_212] :
      ( v1_xboole_0(k6_partfun1(A_212))
      | ~ v1_xboole_0(A_212) ) ),
    inference(resolution,[status(thm)],[c_40,c_216])).

tff(c_104,plain,(
    ! [B_51,A_52] :
      ( ~ v1_xboole_0(B_51)
      | B_51 = A_52
      | ~ v1_xboole_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_107,plain,(
    ! [A_52] :
      ( k1_xboole_0 = A_52
      | ~ v1_xboole_0(A_52) ) ),
    inference(resolution,[status(thm)],[c_2,c_104])).

tff(c_1183,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1176,c_107])).

tff(c_1177,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_233])).

tff(c_1190,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1177,c_107])).

tff(c_1207,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1183,c_1190])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | B_2 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1191,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_1177,c_4])).

tff(c_1276,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1207,c_1191])).

tff(c_1355,plain,(
    ! [A_213] :
      ( k6_partfun1(A_213) = '#skF_4'
      | ~ v1_xboole_0(A_213) ) ),
    inference(resolution,[status(thm)],[c_1346,c_1276])).

tff(c_1363,plain,(
    k6_partfun1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1176,c_1355])).

tff(c_1386,plain,(
    v2_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1363,c_65])).

tff(c_10,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1199,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_4',B_4) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1183,c_1183,c_10])).

tff(c_1213,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1207,c_60])).

tff(c_1354,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1199,c_1213])).

tff(c_8,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_231,plain,(
    ! [C_74] :
      ( v1_xboole_0(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_216])).

tff(c_236,plain,(
    ! [C_74] :
      ( v1_xboole_0(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_231])).

tff(c_1425,plain,(
    ! [C_218] :
      ( v1_xboole_0(C_218)
      | ~ m1_subset_1(C_218,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1183,c_236])).

tff(c_1432,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1354,c_1425])).

tff(c_1444,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1432,c_1276])).

tff(c_1453,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1444,c_103])).

tff(c_1462,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1386,c_1453])).

tff(c_1463,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1485,plain,(
    ! [C_223,A_224,B_225] :
      ( v1_relat_1(C_223)
      | ~ m1_subset_1(C_223,k1_zfmisc_1(k2_zfmisc_1(A_224,B_225))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1502,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_1485])).

tff(c_1520,plain,(
    ! [C_229,B_230,A_231] :
      ( v5_relat_1(C_229,B_230)
      | ~ m1_subset_1(C_229,k1_zfmisc_1(k2_zfmisc_1(A_231,B_230))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1538,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_1520])).

tff(c_1704,plain,(
    ! [A_254,B_255,D_256] :
      ( r2_relset_1(A_254,B_255,D_256,D_256)
      | ~ m1_subset_1(D_256,k1_zfmisc_1(k2_zfmisc_1(A_254,B_255))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1715,plain,(
    ! [A_31] : r2_relset_1(A_31,A_31,k6_partfun1(A_31),k6_partfun1(A_31)) ),
    inference(resolution,[status(thm)],[c_40,c_1704])).

tff(c_1788,plain,(
    ! [A_261,B_262,C_263] :
      ( k2_relset_1(A_261,B_262,C_263) = k2_relat_1(C_263)
      | ~ m1_subset_1(C_263,k1_zfmisc_1(k2_zfmisc_1(A_261,B_262))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1806,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_1788])).

tff(c_1830,plain,(
    ! [D_265,C_266,A_267,B_268] :
      ( D_265 = C_266
      | ~ r2_relset_1(A_267,B_268,C_266,D_265)
      | ~ m1_subset_1(D_265,k1_zfmisc_1(k2_zfmisc_1(A_267,B_268)))
      | ~ m1_subset_1(C_266,k1_zfmisc_1(k2_zfmisc_1(A_267,B_268))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1838,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_52,c_1830])).

tff(c_1853,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1838])).

tff(c_2335,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1853])).

tff(c_2561,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_2335])).

tff(c_2565,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_58,c_54,c_2561])).

tff(c_2566,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1853])).

tff(c_2892,plain,(
    ! [A_345,B_346,C_347,D_348] :
      ( k2_relset_1(A_345,B_346,C_347) = B_346
      | ~ r2_relset_1(B_346,B_346,k1_partfun1(B_346,A_345,A_345,B_346,D_348,C_347),k6_partfun1(B_346))
      | ~ m1_subset_1(D_348,k1_zfmisc_1(k2_zfmisc_1(B_346,A_345)))
      | ~ v1_funct_2(D_348,B_346,A_345)
      | ~ v1_funct_1(D_348)
      | ~ m1_subset_1(C_347,k1_zfmisc_1(k2_zfmisc_1(A_345,B_346)))
      | ~ v1_funct_2(C_347,A_345,B_346)
      | ~ v1_funct_1(C_347) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_2895,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2566,c_2892])).

tff(c_2909,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_64,c_62,c_60,c_1715,c_1806,c_2895])).

tff(c_30,plain,(
    ! [B_24] :
      ( v2_funct_2(B_24,k2_relat_1(B_24))
      | ~ v5_relat_1(B_24,k2_relat_1(B_24))
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2915,plain,
    ( v2_funct_2('#skF_4',k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2909,c_30])).

tff(c_2919,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1502,c_1538,c_2909,c_2915])).

tff(c_2921,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1463,c_2919])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:36:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.74/1.87  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.74/1.88  
% 4.74/1.88  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.74/1.88  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.74/1.88  
% 4.74/1.88  %Foreground sorts:
% 4.74/1.88  
% 4.74/1.88  
% 4.74/1.88  %Background operators:
% 4.74/1.88  
% 4.74/1.88  
% 4.74/1.88  %Foreground operators:
% 4.74/1.88  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.74/1.88  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.74/1.88  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.74/1.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.74/1.88  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.74/1.88  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.74/1.88  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.74/1.88  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.74/1.88  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.74/1.88  tff('#skF_2', type, '#skF_2': $i).
% 4.74/1.88  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.74/1.88  tff('#skF_3', type, '#skF_3': $i).
% 4.74/1.88  tff('#skF_1', type, '#skF_1': $i).
% 4.74/1.88  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 4.74/1.88  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.74/1.88  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.74/1.88  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.74/1.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.74/1.88  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.74/1.88  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.74/1.88  tff('#skF_4', type, '#skF_4': $i).
% 4.74/1.88  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.74/1.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.74/1.88  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.74/1.88  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.74/1.88  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.74/1.88  
% 4.74/1.90  tff(f_158, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 4.74/1.90  tff(f_61, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 4.74/1.90  tff(f_99, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.74/1.90  tff(f_44, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 4.74/1.90  tff(f_93, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 4.74/1.90  tff(f_97, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 4.74/1.90  tff(f_73, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.74/1.90  tff(f_138, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 4.74/1.90  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.74/1.90  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 4.74/1.90  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.74/1.90  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.74/1.90  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.74/1.90  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.74/1.90  tff(f_116, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 4.74/1.90  tff(f_81, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 4.74/1.90  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_158])).
% 4.74/1.90  tff(c_216, plain, (![C_74, B_75, A_76]: (v1_xboole_0(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(B_75, A_76))) | ~v1_xboole_0(A_76))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.74/1.90  tff(c_233, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_54, c_216])).
% 4.74/1.90  tff(c_237, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_233])).
% 4.74/1.90  tff(c_50, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_158])).
% 4.74/1.90  tff(c_103, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_50])).
% 4.74/1.90  tff(c_64, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_158])).
% 4.74/1.90  tff(c_62, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_158])).
% 4.74/1.90  tff(c_60, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_158])).
% 4.74/1.90  tff(c_58, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_158])).
% 4.74/1.90  tff(c_56, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_158])).
% 4.74/1.90  tff(c_42, plain, (![A_32]: (k6_relat_1(A_32)=k6_partfun1(A_32))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.74/1.90  tff(c_14, plain, (![A_5]: (v2_funct_1(k6_relat_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.74/1.90  tff(c_65, plain, (![A_5]: (v2_funct_1(k6_partfun1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_14])).
% 4.74/1.90  tff(c_34, plain, (![A_25, F_30, E_29, C_27, D_28, B_26]: (m1_subset_1(k1_partfun1(A_25, B_26, C_27, D_28, E_29, F_30), k1_zfmisc_1(k2_zfmisc_1(A_25, D_28))) | ~m1_subset_1(F_30, k1_zfmisc_1(k2_zfmisc_1(C_27, D_28))) | ~v1_funct_1(F_30) | ~m1_subset_1(E_29, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))) | ~v1_funct_1(E_29))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.74/1.90  tff(c_40, plain, (![A_31]: (m1_subset_1(k6_partfun1(A_31), k1_zfmisc_1(k2_zfmisc_1(A_31, A_31))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.74/1.90  tff(c_52, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_158])).
% 4.74/1.90  tff(c_394, plain, (![D_90, C_91, A_92, B_93]: (D_90=C_91 | ~r2_relset_1(A_92, B_93, C_91, D_90) | ~m1_subset_1(D_90, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.74/1.90  tff(c_400, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_52, c_394])).
% 4.74/1.90  tff(c_411, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_400])).
% 4.74/1.90  tff(c_414, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_411])).
% 4.74/1.90  tff(c_819, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_414])).
% 4.74/1.90  tff(c_823, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_58, c_54, c_819])).
% 4.74/1.90  tff(c_824, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_411])).
% 4.74/1.90  tff(c_1139, plain, (![C_200, B_199, D_201, A_198, E_202]: (k1_xboole_0=C_200 | v2_funct_1(D_201) | ~v2_funct_1(k1_partfun1(A_198, B_199, B_199, C_200, D_201, E_202)) | ~m1_subset_1(E_202, k1_zfmisc_1(k2_zfmisc_1(B_199, C_200))) | ~v1_funct_2(E_202, B_199, C_200) | ~v1_funct_1(E_202) | ~m1_subset_1(D_201, k1_zfmisc_1(k2_zfmisc_1(A_198, B_199))) | ~v1_funct_2(D_201, A_198, B_199) | ~v1_funct_1(D_201))), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.74/1.90  tff(c_1141, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_824, c_1139])).
% 4.74/1.90  tff(c_1143, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_58, c_56, c_54, c_65, c_1141])).
% 4.74/1.90  tff(c_1144, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_103, c_1143])).
% 4.74/1.90  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.74/1.90  tff(c_1173, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1144, c_2])).
% 4.74/1.90  tff(c_1175, plain, $false, inference(negUnitSimplification, [status(thm)], [c_237, c_1173])).
% 4.74/1.90  tff(c_1176, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_233])).
% 4.74/1.90  tff(c_1346, plain, (![A_212]: (v1_xboole_0(k6_partfun1(A_212)) | ~v1_xboole_0(A_212))), inference(resolution, [status(thm)], [c_40, c_216])).
% 4.74/1.90  tff(c_104, plain, (![B_51, A_52]: (~v1_xboole_0(B_51) | B_51=A_52 | ~v1_xboole_0(A_52))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.74/1.90  tff(c_107, plain, (![A_52]: (k1_xboole_0=A_52 | ~v1_xboole_0(A_52))), inference(resolution, [status(thm)], [c_2, c_104])).
% 4.74/1.90  tff(c_1183, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_1176, c_107])).
% 4.74/1.90  tff(c_1177, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_233])).
% 4.74/1.90  tff(c_1190, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_1177, c_107])).
% 4.74/1.90  tff(c_1207, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1183, c_1190])).
% 4.74/1.90  tff(c_4, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | B_2=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.74/1.90  tff(c_1191, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_1177, c_4])).
% 4.74/1.90  tff(c_1276, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_1207, c_1191])).
% 4.74/1.90  tff(c_1355, plain, (![A_213]: (k6_partfun1(A_213)='#skF_4' | ~v1_xboole_0(A_213))), inference(resolution, [status(thm)], [c_1346, c_1276])).
% 4.74/1.90  tff(c_1363, plain, (k6_partfun1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_1176, c_1355])).
% 4.74/1.90  tff(c_1386, plain, (v2_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1363, c_65])).
% 4.74/1.90  tff(c_10, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.74/1.90  tff(c_1199, plain, (![B_4]: (k2_zfmisc_1('#skF_4', B_4)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1183, c_1183, c_10])).
% 4.74/1.90  tff(c_1213, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1207, c_60])).
% 4.74/1.90  tff(c_1354, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1199, c_1213])).
% 4.74/1.90  tff(c_8, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.74/1.90  tff(c_231, plain, (![C_74]: (v1_xboole_0(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_216])).
% 4.74/1.90  tff(c_236, plain, (![C_74]: (v1_xboole_0(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_231])).
% 4.74/1.90  tff(c_1425, plain, (![C_218]: (v1_xboole_0(C_218) | ~m1_subset_1(C_218, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1183, c_236])).
% 4.74/1.90  tff(c_1432, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_1354, c_1425])).
% 4.74/1.90  tff(c_1444, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_1432, c_1276])).
% 4.74/1.90  tff(c_1453, plain, (~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1444, c_103])).
% 4.74/1.90  tff(c_1462, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1386, c_1453])).
% 4.74/1.90  tff(c_1463, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_50])).
% 4.74/1.90  tff(c_1485, plain, (![C_223, A_224, B_225]: (v1_relat_1(C_223) | ~m1_subset_1(C_223, k1_zfmisc_1(k2_zfmisc_1(A_224, B_225))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.74/1.90  tff(c_1502, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_1485])).
% 4.74/1.90  tff(c_1520, plain, (![C_229, B_230, A_231]: (v5_relat_1(C_229, B_230) | ~m1_subset_1(C_229, k1_zfmisc_1(k2_zfmisc_1(A_231, B_230))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.74/1.90  tff(c_1538, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_54, c_1520])).
% 4.74/1.90  tff(c_1704, plain, (![A_254, B_255, D_256]: (r2_relset_1(A_254, B_255, D_256, D_256) | ~m1_subset_1(D_256, k1_zfmisc_1(k2_zfmisc_1(A_254, B_255))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.74/1.90  tff(c_1715, plain, (![A_31]: (r2_relset_1(A_31, A_31, k6_partfun1(A_31), k6_partfun1(A_31)))), inference(resolution, [status(thm)], [c_40, c_1704])).
% 4.74/1.90  tff(c_1788, plain, (![A_261, B_262, C_263]: (k2_relset_1(A_261, B_262, C_263)=k2_relat_1(C_263) | ~m1_subset_1(C_263, k1_zfmisc_1(k2_zfmisc_1(A_261, B_262))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.74/1.90  tff(c_1806, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_1788])).
% 4.74/1.90  tff(c_1830, plain, (![D_265, C_266, A_267, B_268]: (D_265=C_266 | ~r2_relset_1(A_267, B_268, C_266, D_265) | ~m1_subset_1(D_265, k1_zfmisc_1(k2_zfmisc_1(A_267, B_268))) | ~m1_subset_1(C_266, k1_zfmisc_1(k2_zfmisc_1(A_267, B_268))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.10/1.90  tff(c_1838, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_52, c_1830])).
% 5.10/1.90  tff(c_1853, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1838])).
% 5.10/1.90  tff(c_2335, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1853])).
% 5.10/1.90  tff(c_2561, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_2335])).
% 5.10/1.90  tff(c_2565, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_58, c_54, c_2561])).
% 5.10/1.90  tff(c_2566, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1853])).
% 5.10/1.90  tff(c_2892, plain, (![A_345, B_346, C_347, D_348]: (k2_relset_1(A_345, B_346, C_347)=B_346 | ~r2_relset_1(B_346, B_346, k1_partfun1(B_346, A_345, A_345, B_346, D_348, C_347), k6_partfun1(B_346)) | ~m1_subset_1(D_348, k1_zfmisc_1(k2_zfmisc_1(B_346, A_345))) | ~v1_funct_2(D_348, B_346, A_345) | ~v1_funct_1(D_348) | ~m1_subset_1(C_347, k1_zfmisc_1(k2_zfmisc_1(A_345, B_346))) | ~v1_funct_2(C_347, A_345, B_346) | ~v1_funct_1(C_347))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.10/1.90  tff(c_2895, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2566, c_2892])).
% 5.10/1.90  tff(c_2909, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_64, c_62, c_60, c_1715, c_1806, c_2895])).
% 5.10/1.90  tff(c_30, plain, (![B_24]: (v2_funct_2(B_24, k2_relat_1(B_24)) | ~v5_relat_1(B_24, k2_relat_1(B_24)) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.10/1.90  tff(c_2915, plain, (v2_funct_2('#skF_4', k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2909, c_30])).
% 5.10/1.90  tff(c_2919, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1502, c_1538, c_2909, c_2915])).
% 5.10/1.90  tff(c_2921, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1463, c_2919])).
% 5.10/1.90  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.10/1.90  
% 5.10/1.90  Inference rules
% 5.10/1.90  ----------------------
% 5.10/1.90  #Ref     : 0
% 5.10/1.90  #Sup     : 682
% 5.10/1.90  #Fact    : 0
% 5.10/1.90  #Define  : 0
% 5.10/1.90  #Split   : 11
% 5.10/1.90  #Chain   : 0
% 5.10/1.90  #Close   : 0
% 5.10/1.90  
% 5.10/1.90  Ordering : KBO
% 5.10/1.90  
% 5.10/1.90  Simplification rules
% 5.10/1.90  ----------------------
% 5.10/1.90  #Subsume      : 79
% 5.10/1.90  #Demod        : 524
% 5.10/1.90  #Tautology    : 265
% 5.10/1.90  #SimpNegUnit  : 3
% 5.10/1.90  #BackRed      : 68
% 5.10/1.90  
% 5.10/1.90  #Partial instantiations: 0
% 5.10/1.90  #Strategies tried      : 1
% 5.10/1.90  
% 5.10/1.90  Timing (in seconds)
% 5.10/1.90  ----------------------
% 5.10/1.90  Preprocessing        : 0.35
% 5.10/1.90  Parsing              : 0.18
% 5.10/1.90  CNF conversion       : 0.02
% 5.10/1.90  Main loop            : 0.79
% 5.10/1.90  Inferencing          : 0.27
% 5.10/1.90  Reduction            : 0.28
% 5.10/1.90  Demodulation         : 0.21
% 5.10/1.90  BG Simplification    : 0.03
% 5.10/1.90  Subsumption          : 0.14
% 5.10/1.90  Abstraction          : 0.03
% 5.10/1.90  MUC search           : 0.00
% 5.10/1.90  Cooper               : 0.00
% 5.10/1.90  Total                : 1.17
% 5.10/1.91  Index Insertion      : 0.00
% 5.10/1.91  Index Deletion       : 0.00
% 5.10/1.91  Index Matching       : 0.00
% 5.10/1.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
