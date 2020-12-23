%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:22 EST 2020

% Result     : Theorem 5.51s
% Output     : CNFRefutation 5.51s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 261 expanded)
%              Number of leaves         :   42 ( 111 expanded)
%              Depth                    :    9
%              Number of atoms          :  207 ( 800 expanded)
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

tff(f_155,negated_conjecture,(
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

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_96,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_45,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_90,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_94,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_135,axiom,(
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

tff(f_43,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_113,axiom,(
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

tff(f_78,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_54,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_132,plain,(
    ! [C_65,A_66,B_67] :
      ( v1_xboole_0(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67)))
      | ~ v1_xboole_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_144,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_132])).

tff(c_146,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_144])).

tff(c_44,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_72,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_58,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_56,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_52,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_50,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_36,plain,(
    ! [A_32] : k6_relat_1(A_32) = k6_partfun1(A_32) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_10,plain,(
    ! [A_8] : v2_funct_1(k6_relat_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_59,plain,(
    ! [A_8] : v2_funct_1(k6_partfun1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_10])).

tff(c_28,plain,(
    ! [A_25,F_30,E_29,C_27,D_28,B_26] :
      ( m1_subset_1(k1_partfun1(A_25,B_26,C_27,D_28,E_29,F_30),k1_zfmisc_1(k2_zfmisc_1(A_25,D_28)))
      | ~ m1_subset_1(F_30,k1_zfmisc_1(k2_zfmisc_1(C_27,D_28)))
      | ~ v1_funct_1(F_30)
      | ~ m1_subset_1(E_29,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | ~ v1_funct_1(E_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_34,plain,(
    ! [A_31] : m1_subset_1(k6_partfun1(A_31),k1_zfmisc_1(k2_zfmisc_1(A_31,A_31))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_46,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_341,plain,(
    ! [D_82,C_83,A_84,B_85] :
      ( D_82 = C_83
      | ~ r2_relset_1(A_84,B_85,C_83,D_82)
      | ~ m1_subset_1(D_82,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85)))
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_349,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_46,c_341])).

tff(c_364,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_349])).

tff(c_949,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_364])).

tff(c_1141,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_949])).

tff(c_1145,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_52,c_48,c_1141])).

tff(c_1146,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_364])).

tff(c_1225,plain,(
    ! [B_143,C_144,D_145,A_142,E_146] :
      ( k1_xboole_0 = C_144
      | v2_funct_1(D_145)
      | ~ v2_funct_1(k1_partfun1(A_142,B_143,B_143,C_144,D_145,E_146))
      | ~ m1_subset_1(E_146,k1_zfmisc_1(k2_zfmisc_1(B_143,C_144)))
      | ~ v1_funct_2(E_146,B_143,C_144)
      | ~ v1_funct_1(E_146)
      | ~ m1_subset_1(D_145,k1_zfmisc_1(k2_zfmisc_1(A_142,B_143)))
      | ~ v1_funct_2(D_145,A_142,B_143)
      | ~ v1_funct_1(D_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1227,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1146,c_1225])).

tff(c_1229,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_50,c_48,c_59,c_1227])).

tff(c_1230,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1229])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1256,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1230,c_2])).

tff(c_1258,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_1256])).

tff(c_1260,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_73,plain,(
    ! [B_50,A_51] :
      ( ~ v1_xboole_0(B_50)
      | B_50 = A_51
      | ~ v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_76,plain,(
    ! [A_51] :
      ( k1_xboole_0 = A_51
      | ~ v1_xboole_0(A_51) ) ),
    inference(resolution,[status(thm)],[c_2,c_73])).

tff(c_1273,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1260,c_76])).

tff(c_1259,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_1266,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1259,c_76])).

tff(c_1282,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1273,c_1266])).

tff(c_1293,plain,(
    ~ v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1282,c_72])).

tff(c_1310,plain,(
    ! [A_149] :
      ( v1_xboole_0(k6_partfun1(A_149))
      | ~ v1_xboole_0(A_149) ) ),
    inference(resolution,[status(thm)],[c_34,c_132])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | B_2 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1274,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_1260,c_4])).

tff(c_1318,plain,(
    ! [A_150] :
      ( k6_partfun1(A_150) = '#skF_1'
      | ~ v1_xboole_0(A_150) ) ),
    inference(resolution,[status(thm)],[c_1310,c_1274])).

tff(c_1326,plain,(
    k6_partfun1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1260,c_1318])).

tff(c_1346,plain,(
    v2_funct_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1326,c_59])).

tff(c_1354,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1293,c_1346])).

tff(c_1355,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1368,plain,(
    ! [B_155,A_156] :
      ( v1_relat_1(B_155)
      | ~ m1_subset_1(B_155,k1_zfmisc_1(A_156))
      | ~ v1_relat_1(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1377,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_48,c_1368])).

tff(c_1386,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1377])).

tff(c_1402,plain,(
    ! [C_162,B_163,A_164] :
      ( v5_relat_1(C_162,B_163)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(k2_zfmisc_1(A_164,B_163))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1414,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_1402])).

tff(c_1576,plain,(
    ! [A_176,B_177,D_178] :
      ( r2_relset_1(A_176,B_177,D_178,D_178)
      | ~ m1_subset_1(D_178,k1_zfmisc_1(k2_zfmisc_1(A_176,B_177))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1586,plain,(
    ! [A_31] : r2_relset_1(A_31,A_31,k6_partfun1(A_31),k6_partfun1(A_31)) ),
    inference(resolution,[status(thm)],[c_34,c_1576])).

tff(c_1589,plain,(
    ! [A_179,B_180,C_181] :
      ( k2_relset_1(A_179,B_180,C_181) = k2_relat_1(C_181)
      | ~ m1_subset_1(C_181,k1_zfmisc_1(k2_zfmisc_1(A_179,B_180))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1605,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_1589])).

tff(c_1641,plain,(
    ! [D_184,C_185,A_186,B_187] :
      ( D_184 = C_185
      | ~ r2_relset_1(A_186,B_187,C_185,D_184)
      | ~ m1_subset_1(D_184,k1_zfmisc_1(k2_zfmisc_1(A_186,B_187)))
      | ~ m1_subset_1(C_185,k1_zfmisc_1(k2_zfmisc_1(A_186,B_187))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1649,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_46,c_1641])).

tff(c_1664,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1649])).

tff(c_1690,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1664])).

tff(c_2365,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_1690])).

tff(c_2369,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_52,c_48,c_2365])).

tff(c_2370,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1664])).

tff(c_4566,plain,(
    ! [A_313,B_314,C_315,D_316] :
      ( k2_relset_1(A_313,B_314,C_315) = B_314
      | ~ r2_relset_1(B_314,B_314,k1_partfun1(B_314,A_313,A_313,B_314,D_316,C_315),k6_partfun1(B_314))
      | ~ m1_subset_1(D_316,k1_zfmisc_1(k2_zfmisc_1(B_314,A_313)))
      | ~ v1_funct_2(D_316,B_314,A_313)
      | ~ v1_funct_1(D_316)
      | ~ m1_subset_1(C_315,k1_zfmisc_1(k2_zfmisc_1(A_313,B_314)))
      | ~ v1_funct_2(C_315,A_313,B_314)
      | ~ v1_funct_1(C_315) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_4584,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2370,c_4566])).

tff(c_4592,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_58,c_56,c_54,c_1586,c_1605,c_4584])).

tff(c_24,plain,(
    ! [B_24] :
      ( v2_funct_2(B_24,k2_relat_1(B_24))
      | ~ v5_relat_1(B_24,k2_relat_1(B_24))
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_4597,plain,
    ( v2_funct_2('#skF_4',k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4592,c_24])).

tff(c_4601,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1386,c_1414,c_4592,c_4597])).

tff(c_4603,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1355,c_4601])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:28:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.51/1.93  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.51/1.94  
% 5.51/1.94  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.51/1.94  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.51/1.94  
% 5.51/1.94  %Foreground sorts:
% 5.51/1.94  
% 5.51/1.94  
% 5.51/1.94  %Background operators:
% 5.51/1.94  
% 5.51/1.94  
% 5.51/1.94  %Foreground operators:
% 5.51/1.94  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.51/1.94  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.51/1.94  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.51/1.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.51/1.94  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.51/1.94  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.51/1.94  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.51/1.94  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.51/1.94  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.51/1.94  tff('#skF_2', type, '#skF_2': $i).
% 5.51/1.94  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.51/1.94  tff('#skF_3', type, '#skF_3': $i).
% 5.51/1.94  tff('#skF_1', type, '#skF_1': $i).
% 5.51/1.94  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.51/1.94  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.51/1.94  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.51/1.94  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.51/1.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.51/1.94  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.51/1.94  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.51/1.94  tff('#skF_4', type, '#skF_4': $i).
% 5.51/1.94  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.51/1.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.51/1.94  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.51/1.94  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.51/1.94  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.51/1.94  
% 5.51/1.96  tff(f_155, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 5.51/1.96  tff(f_58, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 5.51/1.96  tff(f_96, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.51/1.96  tff(f_45, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_funct_1)).
% 5.51/1.96  tff(f_90, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 5.51/1.96  tff(f_94, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 5.51/1.96  tff(f_70, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.51/1.96  tff(f_135, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 5.51/1.96  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.51/1.96  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 5.51/1.96  tff(f_43, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.51/1.96  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.51/1.96  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.51/1.96  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.51/1.96  tff(f_113, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 5.51/1.96  tff(f_78, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 5.51/1.96  tff(c_54, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.51/1.96  tff(c_132, plain, (![C_65, A_66, B_67]: (v1_xboole_0(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))) | ~v1_xboole_0(A_66))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.51/1.96  tff(c_144, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_54, c_132])).
% 5.51/1.96  tff(c_146, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_144])).
% 5.51/1.96  tff(c_44, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.51/1.96  tff(c_72, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_44])).
% 5.51/1.96  tff(c_58, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.51/1.96  tff(c_56, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.51/1.96  tff(c_52, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.51/1.96  tff(c_50, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.51/1.96  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.51/1.96  tff(c_36, plain, (![A_32]: (k6_relat_1(A_32)=k6_partfun1(A_32))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.51/1.96  tff(c_10, plain, (![A_8]: (v2_funct_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.51/1.96  tff(c_59, plain, (![A_8]: (v2_funct_1(k6_partfun1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_10])).
% 5.51/1.96  tff(c_28, plain, (![A_25, F_30, E_29, C_27, D_28, B_26]: (m1_subset_1(k1_partfun1(A_25, B_26, C_27, D_28, E_29, F_30), k1_zfmisc_1(k2_zfmisc_1(A_25, D_28))) | ~m1_subset_1(F_30, k1_zfmisc_1(k2_zfmisc_1(C_27, D_28))) | ~v1_funct_1(F_30) | ~m1_subset_1(E_29, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))) | ~v1_funct_1(E_29))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.51/1.96  tff(c_34, plain, (![A_31]: (m1_subset_1(k6_partfun1(A_31), k1_zfmisc_1(k2_zfmisc_1(A_31, A_31))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.51/1.96  tff(c_46, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.51/1.96  tff(c_341, plain, (![D_82, C_83, A_84, B_85]: (D_82=C_83 | ~r2_relset_1(A_84, B_85, C_83, D_82) | ~m1_subset_1(D_82, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.51/1.96  tff(c_349, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_46, c_341])).
% 5.51/1.96  tff(c_364, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_349])).
% 5.51/1.96  tff(c_949, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_364])).
% 5.51/1.96  tff(c_1141, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_949])).
% 5.51/1.96  tff(c_1145, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_52, c_48, c_1141])).
% 5.51/1.96  tff(c_1146, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_364])).
% 5.51/1.96  tff(c_1225, plain, (![B_143, C_144, D_145, A_142, E_146]: (k1_xboole_0=C_144 | v2_funct_1(D_145) | ~v2_funct_1(k1_partfun1(A_142, B_143, B_143, C_144, D_145, E_146)) | ~m1_subset_1(E_146, k1_zfmisc_1(k2_zfmisc_1(B_143, C_144))) | ~v1_funct_2(E_146, B_143, C_144) | ~v1_funct_1(E_146) | ~m1_subset_1(D_145, k1_zfmisc_1(k2_zfmisc_1(A_142, B_143))) | ~v1_funct_2(D_145, A_142, B_143) | ~v1_funct_1(D_145))), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.51/1.96  tff(c_1227, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1146, c_1225])).
% 5.51/1.96  tff(c_1229, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_50, c_48, c_59, c_1227])).
% 5.51/1.96  tff(c_1230, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_72, c_1229])).
% 5.51/1.96  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.51/1.96  tff(c_1256, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1230, c_2])).
% 5.51/1.96  tff(c_1258, plain, $false, inference(negUnitSimplification, [status(thm)], [c_146, c_1256])).
% 5.51/1.96  tff(c_1260, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_144])).
% 5.51/1.96  tff(c_73, plain, (![B_50, A_51]: (~v1_xboole_0(B_50) | B_50=A_51 | ~v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.51/1.96  tff(c_76, plain, (![A_51]: (k1_xboole_0=A_51 | ~v1_xboole_0(A_51))), inference(resolution, [status(thm)], [c_2, c_73])).
% 5.51/1.96  tff(c_1273, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_1260, c_76])).
% 5.51/1.96  tff(c_1259, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_144])).
% 5.51/1.96  tff(c_1266, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1259, c_76])).
% 5.51/1.96  tff(c_1282, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1273, c_1266])).
% 5.51/1.96  tff(c_1293, plain, (~v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1282, c_72])).
% 5.51/1.96  tff(c_1310, plain, (![A_149]: (v1_xboole_0(k6_partfun1(A_149)) | ~v1_xboole_0(A_149))), inference(resolution, [status(thm)], [c_34, c_132])).
% 5.51/1.96  tff(c_4, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | B_2=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.51/1.96  tff(c_1274, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_1260, c_4])).
% 5.51/1.96  tff(c_1318, plain, (![A_150]: (k6_partfun1(A_150)='#skF_1' | ~v1_xboole_0(A_150))), inference(resolution, [status(thm)], [c_1310, c_1274])).
% 5.51/1.96  tff(c_1326, plain, (k6_partfun1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_1260, c_1318])).
% 5.51/1.96  tff(c_1346, plain, (v2_funct_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1326, c_59])).
% 5.51/1.96  tff(c_1354, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1293, c_1346])).
% 5.51/1.96  tff(c_1355, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_44])).
% 5.51/1.96  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.51/1.96  tff(c_1368, plain, (![B_155, A_156]: (v1_relat_1(B_155) | ~m1_subset_1(B_155, k1_zfmisc_1(A_156)) | ~v1_relat_1(A_156))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.51/1.96  tff(c_1377, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_48, c_1368])).
% 5.51/1.96  tff(c_1386, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1377])).
% 5.51/1.96  tff(c_1402, plain, (![C_162, B_163, A_164]: (v5_relat_1(C_162, B_163) | ~m1_subset_1(C_162, k1_zfmisc_1(k2_zfmisc_1(A_164, B_163))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.51/1.96  tff(c_1414, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_48, c_1402])).
% 5.51/1.96  tff(c_1576, plain, (![A_176, B_177, D_178]: (r2_relset_1(A_176, B_177, D_178, D_178) | ~m1_subset_1(D_178, k1_zfmisc_1(k2_zfmisc_1(A_176, B_177))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.51/1.96  tff(c_1586, plain, (![A_31]: (r2_relset_1(A_31, A_31, k6_partfun1(A_31), k6_partfun1(A_31)))), inference(resolution, [status(thm)], [c_34, c_1576])).
% 5.51/1.96  tff(c_1589, plain, (![A_179, B_180, C_181]: (k2_relset_1(A_179, B_180, C_181)=k2_relat_1(C_181) | ~m1_subset_1(C_181, k1_zfmisc_1(k2_zfmisc_1(A_179, B_180))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.51/1.96  tff(c_1605, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_1589])).
% 5.51/1.96  tff(c_1641, plain, (![D_184, C_185, A_186, B_187]: (D_184=C_185 | ~r2_relset_1(A_186, B_187, C_185, D_184) | ~m1_subset_1(D_184, k1_zfmisc_1(k2_zfmisc_1(A_186, B_187))) | ~m1_subset_1(C_185, k1_zfmisc_1(k2_zfmisc_1(A_186, B_187))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.51/1.96  tff(c_1649, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_46, c_1641])).
% 5.51/1.96  tff(c_1664, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1649])).
% 5.51/1.96  tff(c_1690, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1664])).
% 5.51/1.96  tff(c_2365, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_1690])).
% 5.51/1.96  tff(c_2369, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_52, c_48, c_2365])).
% 5.51/1.96  tff(c_2370, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1664])).
% 5.51/1.96  tff(c_4566, plain, (![A_313, B_314, C_315, D_316]: (k2_relset_1(A_313, B_314, C_315)=B_314 | ~r2_relset_1(B_314, B_314, k1_partfun1(B_314, A_313, A_313, B_314, D_316, C_315), k6_partfun1(B_314)) | ~m1_subset_1(D_316, k1_zfmisc_1(k2_zfmisc_1(B_314, A_313))) | ~v1_funct_2(D_316, B_314, A_313) | ~v1_funct_1(D_316) | ~m1_subset_1(C_315, k1_zfmisc_1(k2_zfmisc_1(A_313, B_314))) | ~v1_funct_2(C_315, A_313, B_314) | ~v1_funct_1(C_315))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.51/1.96  tff(c_4584, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2370, c_4566])).
% 5.51/1.96  tff(c_4592, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_58, c_56, c_54, c_1586, c_1605, c_4584])).
% 5.51/1.96  tff(c_24, plain, (![B_24]: (v2_funct_2(B_24, k2_relat_1(B_24)) | ~v5_relat_1(B_24, k2_relat_1(B_24)) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.51/1.96  tff(c_4597, plain, (v2_funct_2('#skF_4', k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4592, c_24])).
% 5.51/1.96  tff(c_4601, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1386, c_1414, c_4592, c_4597])).
% 5.51/1.96  tff(c_4603, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1355, c_4601])).
% 5.51/1.96  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.51/1.96  
% 5.51/1.96  Inference rules
% 5.51/1.96  ----------------------
% 5.51/1.96  #Ref     : 0
% 5.51/1.96  #Sup     : 1232
% 5.51/1.96  #Fact    : 0
% 5.51/1.96  #Define  : 0
% 5.51/1.96  #Split   : 16
% 5.51/1.96  #Chain   : 0
% 5.51/1.96  #Close   : 0
% 5.51/1.96  
% 5.51/1.96  Ordering : KBO
% 5.51/1.96  
% 5.51/1.96  Simplification rules
% 5.51/1.96  ----------------------
% 5.51/1.96  #Subsume      : 320
% 5.51/1.96  #Demod        : 646
% 5.51/1.96  #Tautology    : 250
% 5.51/1.96  #SimpNegUnit  : 4
% 5.51/1.96  #BackRed      : 42
% 5.51/1.96  
% 5.51/1.96  #Partial instantiations: 0
% 5.51/1.96  #Strategies tried      : 1
% 5.51/1.96  
% 5.51/1.96  Timing (in seconds)
% 5.51/1.96  ----------------------
% 5.51/1.96  Preprocessing        : 0.36
% 5.51/1.96  Parsing              : 0.20
% 5.51/1.96  CNF conversion       : 0.02
% 5.51/1.96  Main loop            : 0.90
% 5.51/1.96  Inferencing          : 0.28
% 5.51/1.96  Reduction            : 0.32
% 5.51/1.96  Demodulation         : 0.24
% 5.51/1.96  BG Simplification    : 0.04
% 5.51/1.96  Subsumption          : 0.20
% 5.51/1.96  Abstraction          : 0.04
% 5.51/1.96  MUC search           : 0.00
% 5.51/1.96  Cooper               : 0.00
% 5.51/1.96  Total                : 1.30
% 5.51/1.96  Index Insertion      : 0.00
% 5.51/1.96  Index Deletion       : 0.00
% 5.51/1.96  Index Matching       : 0.00
% 5.51/1.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
