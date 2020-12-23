%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:08 EST 2020

% Result     : Theorem 4.55s
% Output     : CNFRefutation 4.75s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 298 expanded)
%              Number of leaves         :   40 ( 122 expanded)
%              Depth                    :   10
%              Number of atoms          :  201 ( 852 expanded)
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

tff(f_144,negated_conjecture,(
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

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_85,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_32,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_83,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_63,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_124,axiom,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_102,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_50,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_118,plain,(
    ! [C_59,A_60,B_61] :
      ( v1_xboole_0(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61)))
      | ~ v1_xboole_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_129,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_118])).

tff(c_131,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_129])).

tff(c_40,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_73,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_54,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_52,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_48,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_46,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_32,plain,(
    ! [A_29] : k6_relat_1(A_29) = k6_partfun1(A_29) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_6,plain,(
    ! [A_2] : v2_funct_1(k6_relat_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_56,plain,(
    ! [A_2] : v2_funct_1(k6_partfun1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_6])).

tff(c_28,plain,(
    ! [A_23,B_24,F_28,D_26,C_25,E_27] :
      ( m1_subset_1(k1_partfun1(A_23,B_24,C_25,D_26,E_27,F_28),k1_zfmisc_1(k2_zfmisc_1(A_23,D_26)))
      | ~ m1_subset_1(F_28,k1_zfmisc_1(k2_zfmisc_1(C_25,D_26)))
      | ~ v1_funct_1(F_28)
      | ~ m1_subset_1(E_27,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24)))
      | ~ v1_funct_1(E_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_22,plain,(
    ! [A_20] : m1_subset_1(k6_relat_1(A_20),k1_zfmisc_1(k2_zfmisc_1(A_20,A_20))) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_55,plain,(
    ! [A_20] : m1_subset_1(k6_partfun1(A_20),k1_zfmisc_1(k2_zfmisc_1(A_20,A_20))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_22])).

tff(c_42,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_342,plain,(
    ! [D_76,C_77,A_78,B_79] :
      ( D_76 = C_77
      | ~ r2_relset_1(A_78,B_79,C_77,D_76)
      | ~ m1_subset_1(D_76,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79)))
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_352,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_42,c_342])).

tff(c_371,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_352])).

tff(c_913,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_371])).

tff(c_916,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_913])).

tff(c_920,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_48,c_44,c_916])).

tff(c_921,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_371])).

tff(c_958,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_960,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_921,c_958])).

tff(c_962,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_44,c_56,c_960])).

tff(c_963,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_962])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_995,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_963,c_2])).

tff(c_997,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_995])).

tff(c_999,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_129])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_1007,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_999,c_4])).

tff(c_998,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_129])).

tff(c_1003,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_998,c_4])).

tff(c_1016,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1007,c_1003])).

tff(c_1027,plain,(
    ~ v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1016,c_73])).

tff(c_1049,plain,(
    ! [A_129] :
      ( v1_xboole_0(k6_partfun1(A_129))
      | ~ v1_xboole_0(A_129) ) ),
    inference(resolution,[status(thm)],[c_55,c_118])).

tff(c_1009,plain,(
    ! [A_1] :
      ( A_1 = '#skF_3'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1003,c_4])).

tff(c_1042,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1016,c_1009])).

tff(c_1054,plain,(
    ! [A_130] :
      ( k6_partfun1(A_130) = '#skF_1'
      | ~ v1_xboole_0(A_130) ) ),
    inference(resolution,[status(thm)],[c_1049,c_1042])).

tff(c_1062,plain,(
    k6_partfun1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_999,c_1054])).

tff(c_1098,plain,(
    v2_funct_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1062,c_56])).

tff(c_1106,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1027,c_1098])).

tff(c_1107,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_1110,plain,(
    ! [C_134,A_135,B_136] :
      ( v1_relat_1(C_134)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(A_135,B_136))) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1121,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_1110])).

tff(c_1123,plain,(
    ! [C_137,B_138,A_139] :
      ( v5_relat_1(C_137,B_138)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_139,B_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1134,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_1123])).

tff(c_1318,plain,(
    ! [A_157,B_158,D_159] :
      ( r2_relset_1(A_157,B_158,D_159,D_159)
      | ~ m1_subset_1(D_159,k1_zfmisc_1(k2_zfmisc_1(A_157,B_158))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1328,plain,(
    ! [A_20] : r2_relset_1(A_20,A_20,k6_partfun1(A_20),k6_partfun1(A_20)) ),
    inference(resolution,[status(thm)],[c_55,c_1318])).

tff(c_1331,plain,(
    ! [A_160,B_161,C_162] :
      ( k2_relset_1(A_160,B_161,C_162) = k2_relat_1(C_162)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(k2_zfmisc_1(A_160,B_161))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1346,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_1331])).

tff(c_1676,plain,(
    ! [C_187,F_188,B_190,A_192,E_189,D_191] :
      ( m1_subset_1(k1_partfun1(A_192,B_190,C_187,D_191,E_189,F_188),k1_zfmisc_1(k2_zfmisc_1(A_192,D_191)))
      | ~ m1_subset_1(F_188,k1_zfmisc_1(k2_zfmisc_1(C_187,D_191)))
      | ~ v1_funct_1(F_188)
      | ~ m1_subset_1(E_189,k1_zfmisc_1(k2_zfmisc_1(A_192,B_190)))
      | ~ v1_funct_1(E_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1361,plain,(
    ! [D_163,C_164,A_165,B_166] :
      ( D_163 = C_164
      | ~ r2_relset_1(A_165,B_166,C_164,D_163)
      | ~ m1_subset_1(D_163,k1_zfmisc_1(k2_zfmisc_1(A_165,B_166)))
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(A_165,B_166))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1369,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_42,c_1361])).

tff(c_1384,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_1369])).

tff(c_1430,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1384])).

tff(c_1682,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1676,c_1430])).

tff(c_1706,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_48,c_44,c_1682])).

tff(c_1707,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1384])).

tff(c_2563,plain,(
    ! [A_253,B_254,C_255,D_256] :
      ( k2_relset_1(A_253,B_254,C_255) = B_254
      | ~ r2_relset_1(B_254,B_254,k1_partfun1(B_254,A_253,A_253,B_254,D_256,C_255),k6_partfun1(B_254))
      | ~ m1_subset_1(D_256,k1_zfmisc_1(k2_zfmisc_1(B_254,A_253)))
      | ~ v1_funct_2(D_256,B_254,A_253)
      | ~ v1_funct_1(D_256)
      | ~ m1_subset_1(C_255,k1_zfmisc_1(k2_zfmisc_1(A_253,B_254)))
      | ~ v1_funct_2(C_255,A_253,B_254)
      | ~ v1_funct_1(C_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2566,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1707,c_2563])).

tff(c_2574,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_54,c_52,c_50,c_1328,c_1346,c_2566])).

tff(c_24,plain,(
    ! [B_22] :
      ( v2_funct_2(B_22,k2_relat_1(B_22))
      | ~ v5_relat_1(B_22,k2_relat_1(B_22))
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2579,plain,
    ( v2_funct_2('#skF_4',k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2574,c_24])).

tff(c_2583,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1121,c_1134,c_2574,c_2579])).

tff(c_2585,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1107,c_2583])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:19:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.55/1.85  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.75/1.86  
% 4.75/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.75/1.86  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.75/1.86  
% 4.75/1.86  %Foreground sorts:
% 4.75/1.86  
% 4.75/1.86  
% 4.75/1.86  %Background operators:
% 4.75/1.86  
% 4.75/1.86  
% 4.75/1.86  %Foreground operators:
% 4.75/1.86  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.75/1.86  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.75/1.86  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.75/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.75/1.86  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.75/1.86  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.75/1.86  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.75/1.86  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.75/1.86  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.75/1.86  tff('#skF_2', type, '#skF_2': $i).
% 4.75/1.86  tff('#skF_3', type, '#skF_3': $i).
% 4.75/1.86  tff('#skF_1', type, '#skF_1': $i).
% 4.75/1.86  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 4.75/1.86  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.75/1.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.75/1.86  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.75/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.75/1.86  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.75/1.86  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.75/1.86  tff('#skF_4', type, '#skF_4': $i).
% 4.75/1.86  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.75/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.75/1.86  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.75/1.86  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.75/1.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.75/1.86  
% 4.75/1.88  tff(f_144, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 4.75/1.88  tff(f_49, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 4.75/1.88  tff(f_85, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.75/1.88  tff(f_32, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_funct_1)).
% 4.75/1.88  tff(f_83, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 4.75/1.88  tff(f_63, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 4.75/1.88  tff(f_61, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.75/1.88  tff(f_124, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 4.75/1.88  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.75/1.88  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.75/1.88  tff(f_36, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.75/1.88  tff(f_42, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.75/1.88  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.75/1.88  tff(f_102, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 4.75/1.88  tff(f_71, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 4.75/1.88  tff(c_50, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.75/1.88  tff(c_118, plain, (![C_59, A_60, B_61]: (v1_xboole_0(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))) | ~v1_xboole_0(A_60))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.75/1.88  tff(c_129, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_50, c_118])).
% 4.75/1.88  tff(c_131, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_129])).
% 4.75/1.88  tff(c_40, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.75/1.88  tff(c_73, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_40])).
% 4.75/1.88  tff(c_54, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.75/1.88  tff(c_52, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.75/1.88  tff(c_48, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.75/1.88  tff(c_46, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.75/1.88  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.75/1.88  tff(c_32, plain, (![A_29]: (k6_relat_1(A_29)=k6_partfun1(A_29))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.75/1.88  tff(c_6, plain, (![A_2]: (v2_funct_1(k6_relat_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.75/1.88  tff(c_56, plain, (![A_2]: (v2_funct_1(k6_partfun1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_6])).
% 4.75/1.88  tff(c_28, plain, (![A_23, B_24, F_28, D_26, C_25, E_27]: (m1_subset_1(k1_partfun1(A_23, B_24, C_25, D_26, E_27, F_28), k1_zfmisc_1(k2_zfmisc_1(A_23, D_26))) | ~m1_subset_1(F_28, k1_zfmisc_1(k2_zfmisc_1(C_25, D_26))) | ~v1_funct_1(F_28) | ~m1_subset_1(E_27, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))) | ~v1_funct_1(E_27))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.75/1.88  tff(c_22, plain, (![A_20]: (m1_subset_1(k6_relat_1(A_20), k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.75/1.88  tff(c_55, plain, (![A_20]: (m1_subset_1(k6_partfun1(A_20), k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_22])).
% 4.75/1.88  tff(c_42, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.75/1.88  tff(c_342, plain, (![D_76, C_77, A_78, B_79]: (D_76=C_77 | ~r2_relset_1(A_78, B_79, C_77, D_76) | ~m1_subset_1(D_76, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.75/1.88  tff(c_352, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_42, c_342])).
% 4.75/1.88  tff(c_371, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_352])).
% 4.75/1.88  tff(c_913, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_371])).
% 4.75/1.88  tff(c_916, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_913])).
% 4.75/1.88  tff(c_920, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_48, c_44, c_916])).
% 4.75/1.88  tff(c_921, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_371])).
% 4.75/1.88  tff(c_958, plain, (![C_121, D_122, A_120, E_123, B_124]: (k1_xboole_0=C_121 | v2_funct_1(D_122) | ~v2_funct_1(k1_partfun1(A_120, B_124, B_124, C_121, D_122, E_123)) | ~m1_subset_1(E_123, k1_zfmisc_1(k2_zfmisc_1(B_124, C_121))) | ~v1_funct_2(E_123, B_124, C_121) | ~v1_funct_1(E_123) | ~m1_subset_1(D_122, k1_zfmisc_1(k2_zfmisc_1(A_120, B_124))) | ~v1_funct_2(D_122, A_120, B_124) | ~v1_funct_1(D_122))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.75/1.88  tff(c_960, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_921, c_958])).
% 4.75/1.88  tff(c_962, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_46, c_44, c_56, c_960])).
% 4.75/1.88  tff(c_963, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_73, c_962])).
% 4.75/1.88  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.75/1.88  tff(c_995, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_963, c_2])).
% 4.75/1.88  tff(c_997, plain, $false, inference(negUnitSimplification, [status(thm)], [c_131, c_995])).
% 4.75/1.88  tff(c_999, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_129])).
% 4.75/1.88  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 4.75/1.88  tff(c_1007, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_999, c_4])).
% 4.75/1.88  tff(c_998, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_129])).
% 4.75/1.88  tff(c_1003, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_998, c_4])).
% 4.75/1.88  tff(c_1016, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1007, c_1003])).
% 4.75/1.88  tff(c_1027, plain, (~v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1016, c_73])).
% 4.75/1.88  tff(c_1049, plain, (![A_129]: (v1_xboole_0(k6_partfun1(A_129)) | ~v1_xboole_0(A_129))), inference(resolution, [status(thm)], [c_55, c_118])).
% 4.75/1.88  tff(c_1009, plain, (![A_1]: (A_1='#skF_3' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_1003, c_4])).
% 4.75/1.88  tff(c_1042, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_1016, c_1009])).
% 4.75/1.88  tff(c_1054, plain, (![A_130]: (k6_partfun1(A_130)='#skF_1' | ~v1_xboole_0(A_130))), inference(resolution, [status(thm)], [c_1049, c_1042])).
% 4.75/1.88  tff(c_1062, plain, (k6_partfun1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_999, c_1054])).
% 4.75/1.88  tff(c_1098, plain, (v2_funct_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1062, c_56])).
% 4.75/1.88  tff(c_1106, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1027, c_1098])).
% 4.75/1.88  tff(c_1107, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_40])).
% 4.75/1.88  tff(c_1110, plain, (![C_134, A_135, B_136]: (v1_relat_1(C_134) | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(A_135, B_136))))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.75/1.88  tff(c_1121, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_1110])).
% 4.75/1.88  tff(c_1123, plain, (![C_137, B_138, A_139]: (v5_relat_1(C_137, B_138) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_139, B_138))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.75/1.88  tff(c_1134, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_44, c_1123])).
% 4.75/1.88  tff(c_1318, plain, (![A_157, B_158, D_159]: (r2_relset_1(A_157, B_158, D_159, D_159) | ~m1_subset_1(D_159, k1_zfmisc_1(k2_zfmisc_1(A_157, B_158))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.75/1.88  tff(c_1328, plain, (![A_20]: (r2_relset_1(A_20, A_20, k6_partfun1(A_20), k6_partfun1(A_20)))), inference(resolution, [status(thm)], [c_55, c_1318])).
% 4.75/1.88  tff(c_1331, plain, (![A_160, B_161, C_162]: (k2_relset_1(A_160, B_161, C_162)=k2_relat_1(C_162) | ~m1_subset_1(C_162, k1_zfmisc_1(k2_zfmisc_1(A_160, B_161))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.75/1.88  tff(c_1346, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_1331])).
% 4.75/1.88  tff(c_1676, plain, (![C_187, F_188, B_190, A_192, E_189, D_191]: (m1_subset_1(k1_partfun1(A_192, B_190, C_187, D_191, E_189, F_188), k1_zfmisc_1(k2_zfmisc_1(A_192, D_191))) | ~m1_subset_1(F_188, k1_zfmisc_1(k2_zfmisc_1(C_187, D_191))) | ~v1_funct_1(F_188) | ~m1_subset_1(E_189, k1_zfmisc_1(k2_zfmisc_1(A_192, B_190))) | ~v1_funct_1(E_189))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.75/1.88  tff(c_1361, plain, (![D_163, C_164, A_165, B_166]: (D_163=C_164 | ~r2_relset_1(A_165, B_166, C_164, D_163) | ~m1_subset_1(D_163, k1_zfmisc_1(k2_zfmisc_1(A_165, B_166))) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(A_165, B_166))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.75/1.88  tff(c_1369, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_42, c_1361])).
% 4.75/1.88  tff(c_1384, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_1369])).
% 4.75/1.88  tff(c_1430, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1384])).
% 4.75/1.88  tff(c_1682, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1676, c_1430])).
% 4.75/1.88  tff(c_1706, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_48, c_44, c_1682])).
% 4.75/1.88  tff(c_1707, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1384])).
% 4.75/1.88  tff(c_2563, plain, (![A_253, B_254, C_255, D_256]: (k2_relset_1(A_253, B_254, C_255)=B_254 | ~r2_relset_1(B_254, B_254, k1_partfun1(B_254, A_253, A_253, B_254, D_256, C_255), k6_partfun1(B_254)) | ~m1_subset_1(D_256, k1_zfmisc_1(k2_zfmisc_1(B_254, A_253))) | ~v1_funct_2(D_256, B_254, A_253) | ~v1_funct_1(D_256) | ~m1_subset_1(C_255, k1_zfmisc_1(k2_zfmisc_1(A_253, B_254))) | ~v1_funct_2(C_255, A_253, B_254) | ~v1_funct_1(C_255))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.75/1.88  tff(c_2566, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1707, c_2563])).
% 4.75/1.88  tff(c_2574, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_54, c_52, c_50, c_1328, c_1346, c_2566])).
% 4.75/1.88  tff(c_24, plain, (![B_22]: (v2_funct_2(B_22, k2_relat_1(B_22)) | ~v5_relat_1(B_22, k2_relat_1(B_22)) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.75/1.88  tff(c_2579, plain, (v2_funct_2('#skF_4', k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2574, c_24])).
% 4.75/1.88  tff(c_2583, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1121, c_1134, c_2574, c_2579])).
% 4.75/1.88  tff(c_2585, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1107, c_2583])).
% 4.75/1.88  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.75/1.88  
% 4.75/1.88  Inference rules
% 4.75/1.88  ----------------------
% 4.75/1.88  #Ref     : 0
% 4.75/1.88  #Sup     : 586
% 4.75/1.88  #Fact    : 0
% 4.75/1.88  #Define  : 0
% 4.75/1.88  #Split   : 17
% 4.75/1.88  #Chain   : 0
% 4.75/1.88  #Close   : 0
% 4.75/1.88  
% 4.75/1.88  Ordering : KBO
% 4.75/1.88  
% 4.75/1.88  Simplification rules
% 4.75/1.88  ----------------------
% 4.75/1.88  #Subsume      : 110
% 4.75/1.88  #Demod        : 690
% 4.75/1.88  #Tautology    : 243
% 4.75/1.88  #SimpNegUnit  : 4
% 4.75/1.88  #BackRed      : 48
% 4.75/1.88  
% 4.75/1.88  #Partial instantiations: 0
% 4.75/1.88  #Strategies tried      : 1
% 4.75/1.88  
% 4.75/1.88  Timing (in seconds)
% 4.75/1.88  ----------------------
% 4.75/1.88  Preprocessing        : 0.36
% 4.75/1.88  Parsing              : 0.20
% 4.75/1.88  CNF conversion       : 0.02
% 4.75/1.88  Main loop            : 0.69
% 4.75/1.88  Inferencing          : 0.24
% 4.75/1.88  Reduction            : 0.25
% 4.75/1.88  Demodulation         : 0.18
% 4.75/1.88  BG Simplification    : 0.03
% 4.75/1.88  Subsumption          : 0.12
% 4.75/1.88  Abstraction          : 0.03
% 4.75/1.88  MUC search           : 0.00
% 4.75/1.88  Cooper               : 0.00
% 4.75/1.89  Total                : 1.10
% 4.75/1.89  Index Insertion      : 0.00
% 4.75/1.89  Index Deletion       : 0.00
% 4.75/1.89  Index Matching       : 0.00
% 4.75/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
