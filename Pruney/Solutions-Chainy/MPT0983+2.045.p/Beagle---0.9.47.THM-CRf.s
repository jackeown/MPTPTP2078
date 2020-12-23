%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:07 EST 2020

% Result     : Theorem 4.91s
% Output     : CNFRefutation 5.24s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 258 expanded)
%              Number of leaves         :   41 ( 110 expanded)
%              Depth                    :    9
%              Number of atoms          :  202 ( 796 expanded)
%              Number of equality atoms :   35 (  64 expanded)
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

tff(f_152,negated_conjecture,(
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

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_93,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_87,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_91,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_132,axiom,(
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

tff(f_42,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_110,axiom,(
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

tff(f_75,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_54,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_128,plain,(
    ! [C_63,A_64,B_65] :
      ( v1_xboole_0(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65)))
      | ~ v1_xboole_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_140,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_128])).

tff(c_142,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_140])).

tff(c_44,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_73,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_58,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_56,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_52,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_50,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_36,plain,(
    ! [A_30] : k6_relat_1(A_30) = k6_partfun1(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_8,plain,(
    ! [A_3] : v2_funct_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_59,plain,(
    ! [A_3] : v2_funct_1(k6_partfun1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_8])).

tff(c_28,plain,(
    ! [A_23,B_24,F_28,D_26,C_25,E_27] :
      ( m1_subset_1(k1_partfun1(A_23,B_24,C_25,D_26,E_27,F_28),k1_zfmisc_1(k2_zfmisc_1(A_23,D_26)))
      | ~ m1_subset_1(F_28,k1_zfmisc_1(k2_zfmisc_1(C_25,D_26)))
      | ~ v1_funct_1(F_28)
      | ~ m1_subset_1(E_27,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24)))
      | ~ v1_funct_1(E_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_34,plain,(
    ! [A_29] : m1_subset_1(k6_partfun1(A_29),k1_zfmisc_1(k2_zfmisc_1(A_29,A_29))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_46,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_351,plain,(
    ! [D_80,C_81,A_82,B_83] :
      ( D_80 = C_81
      | ~ r2_relset_1(A_82,B_83,C_81,D_80)
      | ~ m1_subset_1(D_80,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83)))
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_359,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_46,c_351])).

tff(c_374,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_359])).

tff(c_1005,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_374])).

tff(c_1191,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_1005])).

tff(c_1195,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_52,c_48,c_1191])).

tff(c_1196,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_374])).

tff(c_1275,plain,(
    ! [B_143,C_144,D_142,E_141,A_140] :
      ( k1_xboole_0 = C_144
      | v2_funct_1(D_142)
      | ~ v2_funct_1(k1_partfun1(A_140,B_143,B_143,C_144,D_142,E_141))
      | ~ m1_subset_1(E_141,k1_zfmisc_1(k2_zfmisc_1(B_143,C_144)))
      | ~ v1_funct_2(E_141,B_143,C_144)
      | ~ v1_funct_1(E_141)
      | ~ m1_subset_1(D_142,k1_zfmisc_1(k2_zfmisc_1(A_140,B_143)))
      | ~ v1_funct_2(D_142,A_140,B_143)
      | ~ v1_funct_1(D_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1277,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1196,c_1275])).

tff(c_1279,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_50,c_48,c_59,c_1277])).

tff(c_1280,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_1279])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1307,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1280,c_2])).

tff(c_1309,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_1307])).

tff(c_1311,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_140])).

tff(c_74,plain,(
    ! [B_47,A_48] :
      ( ~ v1_xboole_0(B_47)
      | B_47 = A_48
      | ~ v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_77,plain,(
    ! [A_48] :
      ( k1_xboole_0 = A_48
      | ~ v1_xboole_0(A_48) ) ),
    inference(resolution,[status(thm)],[c_2,c_74])).

tff(c_1324,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1311,c_77])).

tff(c_1310,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_140])).

tff(c_1317,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1310,c_77])).

tff(c_1333,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1324,c_1317])).

tff(c_1344,plain,(
    ~ v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1333,c_73])).

tff(c_1400,plain,(
    ! [A_148] :
      ( v1_xboole_0(k6_partfun1(A_148))
      | ~ v1_xboole_0(A_148) ) ),
    inference(resolution,[status(thm)],[c_34,c_128])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | B_2 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1325,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_1311,c_4])).

tff(c_1408,plain,(
    ! [A_149] :
      ( k6_partfun1(A_149) = '#skF_1'
      | ~ v1_xboole_0(A_149) ) ),
    inference(resolution,[status(thm)],[c_1400,c_1325])).

tff(c_1416,plain,(
    k6_partfun1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1311,c_1408])).

tff(c_1444,plain,(
    v2_funct_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1416,c_59])).

tff(c_1453,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1344,c_1444])).

tff(c_1454,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1467,plain,(
    ! [C_157,A_158,B_159] :
      ( v1_relat_1(C_157)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_158,B_159))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1479,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_1467])).

tff(c_1495,plain,(
    ! [C_164,B_165,A_166] :
      ( v5_relat_1(C_164,B_165)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(A_166,B_165))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1506,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_1495])).

tff(c_1658,plain,(
    ! [A_177,B_178,D_179] :
      ( r2_relset_1(A_177,B_178,D_179,D_179)
      | ~ m1_subset_1(D_179,k1_zfmisc_1(k2_zfmisc_1(A_177,B_178))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1668,plain,(
    ! [A_29] : r2_relset_1(A_29,A_29,k6_partfun1(A_29),k6_partfun1(A_29)) ),
    inference(resolution,[status(thm)],[c_34,c_1658])).

tff(c_1671,plain,(
    ! [A_180,B_181,C_182] :
      ( k2_relset_1(A_180,B_181,C_182) = k2_relat_1(C_182)
      | ~ m1_subset_1(C_182,k1_zfmisc_1(k2_zfmisc_1(A_180,B_181))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1686,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_1671])).

tff(c_1732,plain,(
    ! [D_186,C_187,A_188,B_189] :
      ( D_186 = C_187
      | ~ r2_relset_1(A_188,B_189,C_187,D_186)
      | ~ m1_subset_1(D_186,k1_zfmisc_1(k2_zfmisc_1(A_188,B_189)))
      | ~ m1_subset_1(C_187,k1_zfmisc_1(k2_zfmisc_1(A_188,B_189))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1740,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_46,c_1732])).

tff(c_1755,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1740])).

tff(c_1761,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1755])).

tff(c_2454,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_1761])).

tff(c_2458,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_52,c_48,c_2454])).

tff(c_2459,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1755])).

tff(c_3725,plain,(
    ! [A_298,B_299,C_300,D_301] :
      ( k2_relset_1(A_298,B_299,C_300) = B_299
      | ~ r2_relset_1(B_299,B_299,k1_partfun1(B_299,A_298,A_298,B_299,D_301,C_300),k6_partfun1(B_299))
      | ~ m1_subset_1(D_301,k1_zfmisc_1(k2_zfmisc_1(B_299,A_298)))
      | ~ v1_funct_2(D_301,B_299,A_298)
      | ~ v1_funct_1(D_301)
      | ~ m1_subset_1(C_300,k1_zfmisc_1(k2_zfmisc_1(A_298,B_299)))
      | ~ v1_funct_2(C_300,A_298,B_299)
      | ~ v1_funct_1(C_300) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_3737,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2459,c_3725])).

tff(c_3745,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_58,c_56,c_54,c_1668,c_1686,c_3737])).

tff(c_24,plain,(
    ! [B_22] :
      ( v2_funct_2(B_22,k2_relat_1(B_22))
      | ~ v5_relat_1(B_22,k2_relat_1(B_22))
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_3750,plain,
    ( v2_funct_2('#skF_4',k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3745,c_24])).

tff(c_3754,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1479,c_1506,c_3745,c_3750])).

tff(c_3756,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1454,c_3754])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:05:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.91/1.91  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.24/1.92  
% 5.24/1.92  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.24/1.92  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.24/1.92  
% 5.24/1.92  %Foreground sorts:
% 5.24/1.92  
% 5.24/1.92  
% 5.24/1.92  %Background operators:
% 5.24/1.92  
% 5.24/1.92  
% 5.24/1.92  %Foreground operators:
% 5.24/1.92  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.24/1.92  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.24/1.92  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.24/1.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.24/1.92  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.24/1.92  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.24/1.92  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.24/1.92  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.24/1.92  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.24/1.92  tff('#skF_2', type, '#skF_2': $i).
% 5.24/1.92  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.24/1.92  tff('#skF_3', type, '#skF_3': $i).
% 5.24/1.92  tff('#skF_1', type, '#skF_1': $i).
% 5.24/1.92  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.24/1.92  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.24/1.92  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.24/1.92  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.24/1.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.24/1.92  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.24/1.92  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.24/1.92  tff('#skF_4', type, '#skF_4': $i).
% 5.24/1.92  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.24/1.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.24/1.92  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.24/1.92  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.24/1.92  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.24/1.92  
% 5.24/1.94  tff(f_152, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 5.24/1.94  tff(f_55, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 5.24/1.94  tff(f_93, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.24/1.94  tff(f_38, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 5.24/1.94  tff(f_87, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 5.24/1.94  tff(f_91, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 5.24/1.94  tff(f_67, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.24/1.94  tff(f_132, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 5.24/1.94  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.24/1.94  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 5.24/1.94  tff(f_42, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.24/1.94  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.24/1.94  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.24/1.94  tff(f_110, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 5.24/1.94  tff(f_75, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 5.24/1.94  tff(c_54, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_152])).
% 5.24/1.94  tff(c_128, plain, (![C_63, A_64, B_65]: (v1_xboole_0(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))) | ~v1_xboole_0(A_64))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.24/1.94  tff(c_140, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_54, c_128])).
% 5.24/1.94  tff(c_142, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_140])).
% 5.24/1.94  tff(c_44, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_152])).
% 5.24/1.94  tff(c_73, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_44])).
% 5.24/1.94  tff(c_58, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_152])).
% 5.24/1.94  tff(c_56, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 5.24/1.94  tff(c_52, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_152])).
% 5.24/1.94  tff(c_50, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_152])).
% 5.24/1.94  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_152])).
% 5.24/1.94  tff(c_36, plain, (![A_30]: (k6_relat_1(A_30)=k6_partfun1(A_30))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.24/1.94  tff(c_8, plain, (![A_3]: (v2_funct_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.24/1.94  tff(c_59, plain, (![A_3]: (v2_funct_1(k6_partfun1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_8])).
% 5.24/1.94  tff(c_28, plain, (![A_23, B_24, F_28, D_26, C_25, E_27]: (m1_subset_1(k1_partfun1(A_23, B_24, C_25, D_26, E_27, F_28), k1_zfmisc_1(k2_zfmisc_1(A_23, D_26))) | ~m1_subset_1(F_28, k1_zfmisc_1(k2_zfmisc_1(C_25, D_26))) | ~v1_funct_1(F_28) | ~m1_subset_1(E_27, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))) | ~v1_funct_1(E_27))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.24/1.94  tff(c_34, plain, (![A_29]: (m1_subset_1(k6_partfun1(A_29), k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.24/1.94  tff(c_46, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_152])).
% 5.24/1.94  tff(c_351, plain, (![D_80, C_81, A_82, B_83]: (D_80=C_81 | ~r2_relset_1(A_82, B_83, C_81, D_80) | ~m1_subset_1(D_80, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.24/1.94  tff(c_359, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_46, c_351])).
% 5.24/1.94  tff(c_374, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_359])).
% 5.24/1.94  tff(c_1005, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_374])).
% 5.24/1.94  tff(c_1191, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_1005])).
% 5.24/1.94  tff(c_1195, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_52, c_48, c_1191])).
% 5.24/1.94  tff(c_1196, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_374])).
% 5.24/1.94  tff(c_1275, plain, (![B_143, C_144, D_142, E_141, A_140]: (k1_xboole_0=C_144 | v2_funct_1(D_142) | ~v2_funct_1(k1_partfun1(A_140, B_143, B_143, C_144, D_142, E_141)) | ~m1_subset_1(E_141, k1_zfmisc_1(k2_zfmisc_1(B_143, C_144))) | ~v1_funct_2(E_141, B_143, C_144) | ~v1_funct_1(E_141) | ~m1_subset_1(D_142, k1_zfmisc_1(k2_zfmisc_1(A_140, B_143))) | ~v1_funct_2(D_142, A_140, B_143) | ~v1_funct_1(D_142))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.24/1.94  tff(c_1277, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1196, c_1275])).
% 5.24/1.94  tff(c_1279, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_50, c_48, c_59, c_1277])).
% 5.24/1.94  tff(c_1280, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_73, c_1279])).
% 5.24/1.94  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.24/1.94  tff(c_1307, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1280, c_2])).
% 5.24/1.94  tff(c_1309, plain, $false, inference(negUnitSimplification, [status(thm)], [c_142, c_1307])).
% 5.24/1.94  tff(c_1311, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_140])).
% 5.24/1.94  tff(c_74, plain, (![B_47, A_48]: (~v1_xboole_0(B_47) | B_47=A_48 | ~v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.24/1.94  tff(c_77, plain, (![A_48]: (k1_xboole_0=A_48 | ~v1_xboole_0(A_48))), inference(resolution, [status(thm)], [c_2, c_74])).
% 5.24/1.94  tff(c_1324, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_1311, c_77])).
% 5.24/1.94  tff(c_1310, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_140])).
% 5.24/1.94  tff(c_1317, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1310, c_77])).
% 5.24/1.94  tff(c_1333, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1324, c_1317])).
% 5.24/1.94  tff(c_1344, plain, (~v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1333, c_73])).
% 5.24/1.94  tff(c_1400, plain, (![A_148]: (v1_xboole_0(k6_partfun1(A_148)) | ~v1_xboole_0(A_148))), inference(resolution, [status(thm)], [c_34, c_128])).
% 5.24/1.94  tff(c_4, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | B_2=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.24/1.94  tff(c_1325, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_1311, c_4])).
% 5.24/1.94  tff(c_1408, plain, (![A_149]: (k6_partfun1(A_149)='#skF_1' | ~v1_xboole_0(A_149))), inference(resolution, [status(thm)], [c_1400, c_1325])).
% 5.24/1.94  tff(c_1416, plain, (k6_partfun1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_1311, c_1408])).
% 5.24/1.94  tff(c_1444, plain, (v2_funct_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1416, c_59])).
% 5.24/1.94  tff(c_1453, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1344, c_1444])).
% 5.24/1.94  tff(c_1454, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_44])).
% 5.24/1.94  tff(c_1467, plain, (![C_157, A_158, B_159]: (v1_relat_1(C_157) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_158, B_159))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.24/1.94  tff(c_1479, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_1467])).
% 5.24/1.94  tff(c_1495, plain, (![C_164, B_165, A_166]: (v5_relat_1(C_164, B_165) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(A_166, B_165))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.24/1.94  tff(c_1506, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_48, c_1495])).
% 5.24/1.94  tff(c_1658, plain, (![A_177, B_178, D_179]: (r2_relset_1(A_177, B_178, D_179, D_179) | ~m1_subset_1(D_179, k1_zfmisc_1(k2_zfmisc_1(A_177, B_178))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.24/1.94  tff(c_1668, plain, (![A_29]: (r2_relset_1(A_29, A_29, k6_partfun1(A_29), k6_partfun1(A_29)))), inference(resolution, [status(thm)], [c_34, c_1658])).
% 5.24/1.94  tff(c_1671, plain, (![A_180, B_181, C_182]: (k2_relset_1(A_180, B_181, C_182)=k2_relat_1(C_182) | ~m1_subset_1(C_182, k1_zfmisc_1(k2_zfmisc_1(A_180, B_181))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.24/1.94  tff(c_1686, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_1671])).
% 5.24/1.94  tff(c_1732, plain, (![D_186, C_187, A_188, B_189]: (D_186=C_187 | ~r2_relset_1(A_188, B_189, C_187, D_186) | ~m1_subset_1(D_186, k1_zfmisc_1(k2_zfmisc_1(A_188, B_189))) | ~m1_subset_1(C_187, k1_zfmisc_1(k2_zfmisc_1(A_188, B_189))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.24/1.94  tff(c_1740, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_46, c_1732])).
% 5.24/1.94  tff(c_1755, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1740])).
% 5.24/1.94  tff(c_1761, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1755])).
% 5.24/1.94  tff(c_2454, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_1761])).
% 5.24/1.94  tff(c_2458, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_52, c_48, c_2454])).
% 5.24/1.94  tff(c_2459, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1755])).
% 5.24/1.94  tff(c_3725, plain, (![A_298, B_299, C_300, D_301]: (k2_relset_1(A_298, B_299, C_300)=B_299 | ~r2_relset_1(B_299, B_299, k1_partfun1(B_299, A_298, A_298, B_299, D_301, C_300), k6_partfun1(B_299)) | ~m1_subset_1(D_301, k1_zfmisc_1(k2_zfmisc_1(B_299, A_298))) | ~v1_funct_2(D_301, B_299, A_298) | ~v1_funct_1(D_301) | ~m1_subset_1(C_300, k1_zfmisc_1(k2_zfmisc_1(A_298, B_299))) | ~v1_funct_2(C_300, A_298, B_299) | ~v1_funct_1(C_300))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.24/1.94  tff(c_3737, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2459, c_3725])).
% 5.24/1.94  tff(c_3745, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_58, c_56, c_54, c_1668, c_1686, c_3737])).
% 5.24/1.94  tff(c_24, plain, (![B_22]: (v2_funct_2(B_22, k2_relat_1(B_22)) | ~v5_relat_1(B_22, k2_relat_1(B_22)) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.24/1.94  tff(c_3750, plain, (v2_funct_2('#skF_4', k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3745, c_24])).
% 5.24/1.94  tff(c_3754, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1479, c_1506, c_3745, c_3750])).
% 5.24/1.94  tff(c_3756, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1454, c_3754])).
% 5.24/1.94  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.24/1.94  
% 5.24/1.94  Inference rules
% 5.24/1.94  ----------------------
% 5.24/1.94  #Ref     : 0
% 5.24/1.94  #Sup     : 967
% 5.24/1.94  #Fact    : 0
% 5.24/1.94  #Define  : 0
% 5.24/1.94  #Split   : 17
% 5.24/1.94  #Chain   : 0
% 5.24/1.94  #Close   : 0
% 5.24/1.94  
% 5.24/1.94  Ordering : KBO
% 5.24/1.94  
% 5.24/1.94  Simplification rules
% 5.24/1.94  ----------------------
% 5.24/1.94  #Subsume      : 210
% 5.24/1.94  #Demod        : 578
% 5.24/1.94  #Tautology    : 242
% 5.24/1.94  #SimpNegUnit  : 4
% 5.24/1.94  #BackRed      : 43
% 5.24/1.94  
% 5.24/1.94  #Partial instantiations: 0
% 5.24/1.94  #Strategies tried      : 1
% 5.24/1.94  
% 5.24/1.94  Timing (in seconds)
% 5.24/1.94  ----------------------
% 5.24/1.94  Preprocessing        : 0.34
% 5.24/1.94  Parsing              : 0.18
% 5.24/1.94  CNF conversion       : 0.02
% 5.24/1.94  Main loop            : 0.84
% 5.24/1.94  Inferencing          : 0.28
% 5.24/1.94  Reduction            : 0.28
% 5.24/1.94  Demodulation         : 0.20
% 5.24/1.94  BG Simplification    : 0.03
% 5.24/1.94  Subsumption          : 0.17
% 5.24/1.95  Abstraction          : 0.04
% 5.24/1.95  MUC search           : 0.00
% 5.24/1.95  Cooper               : 0.00
% 5.24/1.95  Total                : 1.22
% 5.24/1.95  Index Insertion      : 0.00
% 5.24/1.95  Index Deletion       : 0.00
% 5.24/1.95  Index Matching       : 0.00
% 5.24/1.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
