%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:08 EST 2020

% Result     : Theorem 4.58s
% Output     : CNFRefutation 4.76s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 298 expanded)
%              Number of leaves         :   40 ( 122 expanded)
%              Depth                    :   10
%              Number of atoms          :  202 ( 854 expanded)
%              Number of equality atoms :   34 (  89 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_146,negated_conjecture,(
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

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_87,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_34,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_85,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_65,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_126,axiom,(
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

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_104,axiom,(
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

tff(f_73,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_52,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_122,plain,(
    ! [C_59,A_60,B_61] :
      ( v1_xboole_0(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61)))
      | ~ v1_xboole_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_133,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_122])).

tff(c_135,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_133])).

tff(c_42,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_77,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_56,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_54,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_50,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_48,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_34,plain,(
    ! [A_29] : k6_relat_1(A_29) = k6_partfun1(A_29) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_8,plain,(
    ! [A_2] : v2_funct_1(k6_relat_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_58,plain,(
    ! [A_2] : v2_funct_1(k6_partfun1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_8])).

tff(c_30,plain,(
    ! [A_23,B_24,F_28,D_26,C_25,E_27] :
      ( m1_subset_1(k1_partfun1(A_23,B_24,C_25,D_26,E_27,F_28),k1_zfmisc_1(k2_zfmisc_1(A_23,D_26)))
      | ~ m1_subset_1(F_28,k1_zfmisc_1(k2_zfmisc_1(C_25,D_26)))
      | ~ v1_funct_1(F_28)
      | ~ m1_subset_1(E_27,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24)))
      | ~ v1_funct_1(E_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_24,plain,(
    ! [A_20] : m1_subset_1(k6_relat_1(A_20),k1_zfmisc_1(k2_zfmisc_1(A_20,A_20))) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_57,plain,(
    ! [A_20] : m1_subset_1(k6_partfun1(A_20),k1_zfmisc_1(k2_zfmisc_1(A_20,A_20))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_24])).

tff(c_44,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_346,plain,(
    ! [D_76,C_77,A_78,B_79] :
      ( D_76 = C_77
      | ~ r2_relset_1(A_78,B_79,C_77,D_76)
      | ~ m1_subset_1(D_76,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79)))
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_356,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_44,c_346])).

tff(c_375,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_356])).

tff(c_917,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_375])).

tff(c_920,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_917])).

tff(c_924,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_50,c_46,c_920])).

tff(c_925,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_375])).

tff(c_962,plain,(
    ! [C_121,D_122,A_120,E_123,B_124] :
      ( k1_xboole_0 = C_121
      | v2_funct_1(D_122)
      | ~ v2_funct_1(k1_partfun1(A_120,B_124,B_124,C_121,D_122,E_123))
      | ~ m1_subset_1(E_123,k1_zfmisc_1(k2_zfmisc_1(B_124,C_121)))
      | ~ v1_funct_2(E_123,B_124,C_121)
      | ~ v1_funct_1(E_123)
      | ~ m1_subset_1(D_122,k1_zfmisc_1(k2_zfmisc_1(A_120,B_124)))
      | ~ v1_funct_2(D_122,A_120,B_124)
      | ~ v1_funct_1(D_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_964,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_925,c_962])).

tff(c_966,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_48,c_46,c_58,c_964])).

tff(c_967,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_966])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_999,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_967,c_2])).

tff(c_1001,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_999])).

tff(c_1003,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_133])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_1011,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1003,c_4])).

tff(c_1002,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_133])).

tff(c_1007,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1002,c_4])).

tff(c_1020,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1011,c_1007])).

tff(c_1031,plain,(
    ~ v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1020,c_77])).

tff(c_1053,plain,(
    ! [A_129] :
      ( v1_xboole_0(k6_partfun1(A_129))
      | ~ v1_xboole_0(A_129) ) ),
    inference(resolution,[status(thm)],[c_57,c_122])).

tff(c_1013,plain,(
    ! [A_1] :
      ( A_1 = '#skF_3'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1007,c_4])).

tff(c_1046,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1020,c_1013])).

tff(c_1058,plain,(
    ! [A_130] :
      ( k6_partfun1(A_130) = '#skF_1'
      | ~ v1_xboole_0(A_130) ) ),
    inference(resolution,[status(thm)],[c_1053,c_1046])).

tff(c_1066,plain,(
    k6_partfun1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1003,c_1058])).

tff(c_1100,plain,(
    v2_funct_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1066,c_58])).

tff(c_1109,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1031,c_1100])).

tff(c_1110,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_1113,plain,(
    ! [C_134,A_135,B_136] :
      ( v1_relat_1(C_134)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(A_135,B_136))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1125,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_1113])).

tff(c_1141,plain,(
    ! [C_141,B_142,A_143] :
      ( v5_relat_1(C_141,B_142)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_143,B_142))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1152,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_1141])).

tff(c_1207,plain,(
    ! [A_151,B_152,D_153] :
      ( r2_relset_1(A_151,B_152,D_153,D_153)
      | ~ m1_subset_1(D_153,k1_zfmisc_1(k2_zfmisc_1(A_151,B_152))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1214,plain,(
    ! [A_20] : r2_relset_1(A_20,A_20,k6_partfun1(A_20),k6_partfun1(A_20)) ),
    inference(resolution,[status(thm)],[c_57,c_1207])).

tff(c_1335,plain,(
    ! [A_159,B_160,C_161] :
      ( k2_relset_1(A_159,B_160,C_161) = k2_relat_1(C_161)
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(A_159,B_160))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1350,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_1335])).

tff(c_1735,plain,(
    ! [C_187,F_188,B_190,A_192,E_189,D_191] :
      ( m1_subset_1(k1_partfun1(A_192,B_190,C_187,D_191,E_189,F_188),k1_zfmisc_1(k2_zfmisc_1(A_192,D_191)))
      | ~ m1_subset_1(F_188,k1_zfmisc_1(k2_zfmisc_1(C_187,D_191)))
      | ~ v1_funct_1(F_188)
      | ~ m1_subset_1(E_189,k1_zfmisc_1(k2_zfmisc_1(A_192,B_190)))
      | ~ v1_funct_1(E_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1379,plain,(
    ! [D_163,C_164,A_165,B_166] :
      ( D_163 = C_164
      | ~ r2_relset_1(A_165,B_166,C_164,D_163)
      | ~ m1_subset_1(D_163,k1_zfmisc_1(k2_zfmisc_1(A_165,B_166)))
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(A_165,B_166))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1389,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_44,c_1379])).

tff(c_1408,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_1389])).

tff(c_1475,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1408])).

tff(c_1741,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1735,c_1475])).

tff(c_1765,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_50,c_46,c_1741])).

tff(c_1766,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1408])).

tff(c_2586,plain,(
    ! [A_254,B_255,C_256,D_257] :
      ( k2_relset_1(A_254,B_255,C_256) = B_255
      | ~ r2_relset_1(B_255,B_255,k1_partfun1(B_255,A_254,A_254,B_255,D_257,C_256),k6_partfun1(B_255))
      | ~ m1_subset_1(D_257,k1_zfmisc_1(k2_zfmisc_1(B_255,A_254)))
      | ~ v1_funct_2(D_257,B_255,A_254)
      | ~ v1_funct_1(D_257)
      | ~ m1_subset_1(C_256,k1_zfmisc_1(k2_zfmisc_1(A_254,B_255)))
      | ~ v1_funct_2(C_256,A_254,B_255)
      | ~ v1_funct_1(C_256) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2589,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1766,c_2586])).

tff(c_2597,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_56,c_54,c_52,c_1214,c_1350,c_2589])).

tff(c_26,plain,(
    ! [B_22] :
      ( v2_funct_2(B_22,k2_relat_1(B_22))
      | ~ v5_relat_1(B_22,k2_relat_1(B_22))
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2602,plain,
    ( v2_funct_2('#skF_4',k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2597,c_26])).

tff(c_2606,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1125,c_1152,c_2597,c_2602])).

tff(c_2608,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1110,c_2606])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:49:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.58/1.81  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.58/1.82  
% 4.58/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.71/1.82  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.71/1.82  
% 4.71/1.82  %Foreground sorts:
% 4.71/1.82  
% 4.71/1.82  
% 4.71/1.82  %Background operators:
% 4.71/1.82  
% 4.71/1.82  
% 4.71/1.82  %Foreground operators:
% 4.71/1.82  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.71/1.82  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.71/1.82  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.71/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.71/1.82  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.71/1.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.71/1.82  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.71/1.82  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.71/1.82  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.71/1.82  tff('#skF_2', type, '#skF_2': $i).
% 4.71/1.82  tff('#skF_3', type, '#skF_3': $i).
% 4.71/1.82  tff('#skF_1', type, '#skF_1': $i).
% 4.71/1.82  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 4.71/1.82  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.71/1.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.71/1.82  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.71/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.71/1.82  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.71/1.82  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.71/1.82  tff('#skF_4', type, '#skF_4': $i).
% 4.71/1.82  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.71/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.71/1.82  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.71/1.82  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.71/1.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.71/1.82  
% 4.76/1.84  tff(f_146, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 4.76/1.84  tff(f_51, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 4.76/1.84  tff(f_87, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.76/1.84  tff(f_34, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 4.76/1.84  tff(f_85, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 4.76/1.84  tff(f_65, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 4.76/1.84  tff(f_63, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.76/1.84  tff(f_126, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 4.76/1.84  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.76/1.84  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.76/1.84  tff(f_38, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.76/1.84  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.76/1.84  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.76/1.84  tff(f_104, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 4.76/1.84  tff(f_73, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 4.76/1.84  tff(c_52, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.76/1.84  tff(c_122, plain, (![C_59, A_60, B_61]: (v1_xboole_0(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))) | ~v1_xboole_0(A_60))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.76/1.84  tff(c_133, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_52, c_122])).
% 4.76/1.84  tff(c_135, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_133])).
% 4.76/1.84  tff(c_42, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.76/1.84  tff(c_77, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_42])).
% 4.76/1.84  tff(c_56, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.76/1.84  tff(c_54, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.76/1.84  tff(c_50, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.76/1.84  tff(c_48, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.76/1.84  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.76/1.84  tff(c_34, plain, (![A_29]: (k6_relat_1(A_29)=k6_partfun1(A_29))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.76/1.84  tff(c_8, plain, (![A_2]: (v2_funct_1(k6_relat_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.76/1.84  tff(c_58, plain, (![A_2]: (v2_funct_1(k6_partfun1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_8])).
% 4.76/1.84  tff(c_30, plain, (![A_23, B_24, F_28, D_26, C_25, E_27]: (m1_subset_1(k1_partfun1(A_23, B_24, C_25, D_26, E_27, F_28), k1_zfmisc_1(k2_zfmisc_1(A_23, D_26))) | ~m1_subset_1(F_28, k1_zfmisc_1(k2_zfmisc_1(C_25, D_26))) | ~v1_funct_1(F_28) | ~m1_subset_1(E_27, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))) | ~v1_funct_1(E_27))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.76/1.84  tff(c_24, plain, (![A_20]: (m1_subset_1(k6_relat_1(A_20), k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.76/1.84  tff(c_57, plain, (![A_20]: (m1_subset_1(k6_partfun1(A_20), k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_24])).
% 4.76/1.84  tff(c_44, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.76/1.84  tff(c_346, plain, (![D_76, C_77, A_78, B_79]: (D_76=C_77 | ~r2_relset_1(A_78, B_79, C_77, D_76) | ~m1_subset_1(D_76, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.76/1.84  tff(c_356, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_44, c_346])).
% 4.76/1.84  tff(c_375, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_356])).
% 4.76/1.84  tff(c_917, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_375])).
% 4.76/1.84  tff(c_920, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_917])).
% 4.76/1.84  tff(c_924, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_50, c_46, c_920])).
% 4.76/1.84  tff(c_925, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_375])).
% 4.76/1.84  tff(c_962, plain, (![C_121, D_122, A_120, E_123, B_124]: (k1_xboole_0=C_121 | v2_funct_1(D_122) | ~v2_funct_1(k1_partfun1(A_120, B_124, B_124, C_121, D_122, E_123)) | ~m1_subset_1(E_123, k1_zfmisc_1(k2_zfmisc_1(B_124, C_121))) | ~v1_funct_2(E_123, B_124, C_121) | ~v1_funct_1(E_123) | ~m1_subset_1(D_122, k1_zfmisc_1(k2_zfmisc_1(A_120, B_124))) | ~v1_funct_2(D_122, A_120, B_124) | ~v1_funct_1(D_122))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.76/1.84  tff(c_964, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_925, c_962])).
% 4.76/1.84  tff(c_966, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_48, c_46, c_58, c_964])).
% 4.76/1.84  tff(c_967, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_77, c_966])).
% 4.76/1.84  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.76/1.84  tff(c_999, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_967, c_2])).
% 4.76/1.84  tff(c_1001, plain, $false, inference(negUnitSimplification, [status(thm)], [c_135, c_999])).
% 4.76/1.84  tff(c_1003, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_133])).
% 4.76/1.84  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 4.76/1.84  tff(c_1011, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_1003, c_4])).
% 4.76/1.84  tff(c_1002, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_133])).
% 4.76/1.84  tff(c_1007, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1002, c_4])).
% 4.76/1.84  tff(c_1020, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1011, c_1007])).
% 4.76/1.84  tff(c_1031, plain, (~v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1020, c_77])).
% 4.76/1.84  tff(c_1053, plain, (![A_129]: (v1_xboole_0(k6_partfun1(A_129)) | ~v1_xboole_0(A_129))), inference(resolution, [status(thm)], [c_57, c_122])).
% 4.76/1.84  tff(c_1013, plain, (![A_1]: (A_1='#skF_3' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_1007, c_4])).
% 4.76/1.84  tff(c_1046, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_1020, c_1013])).
% 4.76/1.84  tff(c_1058, plain, (![A_130]: (k6_partfun1(A_130)='#skF_1' | ~v1_xboole_0(A_130))), inference(resolution, [status(thm)], [c_1053, c_1046])).
% 4.76/1.84  tff(c_1066, plain, (k6_partfun1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_1003, c_1058])).
% 4.76/1.84  tff(c_1100, plain, (v2_funct_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1066, c_58])).
% 4.76/1.84  tff(c_1109, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1031, c_1100])).
% 4.76/1.84  tff(c_1110, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_42])).
% 4.76/1.84  tff(c_1113, plain, (![C_134, A_135, B_136]: (v1_relat_1(C_134) | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(A_135, B_136))))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.76/1.84  tff(c_1125, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_1113])).
% 4.76/1.84  tff(c_1141, plain, (![C_141, B_142, A_143]: (v5_relat_1(C_141, B_142) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_143, B_142))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.76/1.84  tff(c_1152, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_46, c_1141])).
% 4.76/1.84  tff(c_1207, plain, (![A_151, B_152, D_153]: (r2_relset_1(A_151, B_152, D_153, D_153) | ~m1_subset_1(D_153, k1_zfmisc_1(k2_zfmisc_1(A_151, B_152))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.76/1.84  tff(c_1214, plain, (![A_20]: (r2_relset_1(A_20, A_20, k6_partfun1(A_20), k6_partfun1(A_20)))), inference(resolution, [status(thm)], [c_57, c_1207])).
% 4.76/1.84  tff(c_1335, plain, (![A_159, B_160, C_161]: (k2_relset_1(A_159, B_160, C_161)=k2_relat_1(C_161) | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(A_159, B_160))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.76/1.84  tff(c_1350, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_1335])).
% 4.76/1.84  tff(c_1735, plain, (![C_187, F_188, B_190, A_192, E_189, D_191]: (m1_subset_1(k1_partfun1(A_192, B_190, C_187, D_191, E_189, F_188), k1_zfmisc_1(k2_zfmisc_1(A_192, D_191))) | ~m1_subset_1(F_188, k1_zfmisc_1(k2_zfmisc_1(C_187, D_191))) | ~v1_funct_1(F_188) | ~m1_subset_1(E_189, k1_zfmisc_1(k2_zfmisc_1(A_192, B_190))) | ~v1_funct_1(E_189))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.76/1.84  tff(c_1379, plain, (![D_163, C_164, A_165, B_166]: (D_163=C_164 | ~r2_relset_1(A_165, B_166, C_164, D_163) | ~m1_subset_1(D_163, k1_zfmisc_1(k2_zfmisc_1(A_165, B_166))) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(A_165, B_166))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.76/1.84  tff(c_1389, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_44, c_1379])).
% 4.76/1.84  tff(c_1408, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_1389])).
% 4.76/1.84  tff(c_1475, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1408])).
% 4.76/1.84  tff(c_1741, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1735, c_1475])).
% 4.76/1.84  tff(c_1765, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_50, c_46, c_1741])).
% 4.76/1.84  tff(c_1766, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1408])).
% 4.76/1.84  tff(c_2586, plain, (![A_254, B_255, C_256, D_257]: (k2_relset_1(A_254, B_255, C_256)=B_255 | ~r2_relset_1(B_255, B_255, k1_partfun1(B_255, A_254, A_254, B_255, D_257, C_256), k6_partfun1(B_255)) | ~m1_subset_1(D_257, k1_zfmisc_1(k2_zfmisc_1(B_255, A_254))) | ~v1_funct_2(D_257, B_255, A_254) | ~v1_funct_1(D_257) | ~m1_subset_1(C_256, k1_zfmisc_1(k2_zfmisc_1(A_254, B_255))) | ~v1_funct_2(C_256, A_254, B_255) | ~v1_funct_1(C_256))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.76/1.84  tff(c_2589, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1766, c_2586])).
% 4.76/1.84  tff(c_2597, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_56, c_54, c_52, c_1214, c_1350, c_2589])).
% 4.76/1.84  tff(c_26, plain, (![B_22]: (v2_funct_2(B_22, k2_relat_1(B_22)) | ~v5_relat_1(B_22, k2_relat_1(B_22)) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.76/1.84  tff(c_2602, plain, (v2_funct_2('#skF_4', k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2597, c_26])).
% 4.76/1.84  tff(c_2606, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1125, c_1152, c_2597, c_2602])).
% 4.76/1.84  tff(c_2608, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1110, c_2606])).
% 4.76/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.76/1.84  
% 4.76/1.84  Inference rules
% 4.76/1.84  ----------------------
% 4.76/1.84  #Ref     : 0
% 4.76/1.84  #Sup     : 593
% 4.76/1.84  #Fact    : 0
% 4.76/1.84  #Define  : 0
% 4.76/1.84  #Split   : 17
% 4.76/1.84  #Chain   : 0
% 4.76/1.84  #Close   : 0
% 4.76/1.84  
% 4.76/1.84  Ordering : KBO
% 4.76/1.84  
% 4.76/1.84  Simplification rules
% 4.76/1.84  ----------------------
% 4.76/1.84  #Subsume      : 111
% 4.76/1.84  #Demod        : 688
% 4.76/1.84  #Tautology    : 245
% 4.76/1.84  #SimpNegUnit  : 4
% 4.76/1.84  #BackRed      : 48
% 4.76/1.84  
% 4.76/1.84  #Partial instantiations: 0
% 4.76/1.84  #Strategies tried      : 1
% 4.76/1.84  
% 4.76/1.84  Timing (in seconds)
% 4.76/1.84  ----------------------
% 4.76/1.85  Preprocessing        : 0.35
% 4.76/1.85  Parsing              : 0.19
% 4.76/1.85  CNF conversion       : 0.02
% 4.76/1.85  Main loop            : 0.71
% 4.76/1.85  Inferencing          : 0.24
% 4.76/1.85  Reduction            : 0.25
% 4.76/1.85  Demodulation         : 0.18
% 4.76/1.85  BG Simplification    : 0.03
% 4.76/1.85  Subsumption          : 0.13
% 4.76/1.85  Abstraction          : 0.03
% 4.76/1.85  MUC search           : 0.00
% 4.76/1.85  Cooper               : 0.00
% 4.76/1.85  Total                : 1.12
% 4.76/1.85  Index Insertion      : 0.00
% 4.76/1.85  Index Deletion       : 0.00
% 4.76/1.85  Index Matching       : 0.00
% 4.76/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
