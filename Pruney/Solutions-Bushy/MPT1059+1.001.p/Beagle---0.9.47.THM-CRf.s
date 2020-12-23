%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1059+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:21 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 110 expanded)
%              Number of leaves         :   34 (  54 expanded)
%              Depth                    :   12
%              Number of atoms          :  121 ( 276 expanded)
%              Number of equality atoms :   37 (  69 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k7_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_partfun1,type,(
    k7_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_111,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,A,B)
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
               => ! [D] :
                    ( m1_subset_1(D,A)
                   => k7_partfun1(B,C,D) = k3_funct_2(A,B,C,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_2)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_52,axiom,(
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

tff(f_63,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_64,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_91,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(c_42,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_34,plain,(
    m1_subset_1('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_71,plain,(
    ! [C_44,B_45,A_46] :
      ( v5_relat_1(C_44,B_45)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_46,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_75,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_71])).

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_28,plain,(
    ! [A_21,B_22] :
      ( r2_hidden(A_21,B_22)
      | v1_xboole_0(B_22)
      | ~ m1_subset_1(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_61,plain,(
    ! [C_38,A_39,B_40] :
      ( v1_relat_1(C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_65,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_61])).

tff(c_40,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_38,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_76,plain,(
    ! [A_47,B_48,C_49] :
      ( k1_relset_1(A_47,B_48,C_49) = k1_relat_1(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_80,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_76])).

tff(c_95,plain,(
    ! [B_60,A_61,C_62] :
      ( k1_xboole_0 = B_60
      | k1_relset_1(A_61,B_60,C_62) = A_61
      | ~ v1_funct_2(C_62,A_61,B_60)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_61,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_98,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_95])).

tff(c_101,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_80,c_98])).

tff(c_102,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_101])).

tff(c_112,plain,(
    ! [A_63,B_64,C_65] :
      ( k7_partfun1(A_63,B_64,C_65) = k1_funct_1(B_64,C_65)
      | ~ r2_hidden(C_65,k1_relat_1(B_64))
      | ~ v1_funct_1(B_64)
      | ~ v5_relat_1(B_64,A_63)
      | ~ v1_relat_1(B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_114,plain,(
    ! [A_63,C_65] :
      ( k7_partfun1(A_63,'#skF_3',C_65) = k1_funct_1('#skF_3',C_65)
      | ~ r2_hidden(C_65,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v5_relat_1('#skF_3',A_63)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_112])).

tff(c_121,plain,(
    ! [A_66,C_67] :
      ( k7_partfun1(A_66,'#skF_3',C_67) = k1_funct_1('#skF_3',C_67)
      | ~ r2_hidden(C_67,'#skF_1')
      | ~ v5_relat_1('#skF_3',A_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_40,c_114])).

tff(c_124,plain,(
    ! [A_66,A_21] :
      ( k7_partfun1(A_66,'#skF_3',A_21) = k1_funct_1('#skF_3',A_21)
      | ~ v5_relat_1('#skF_3',A_66)
      | v1_xboole_0('#skF_1')
      | ~ m1_subset_1(A_21,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_121])).

tff(c_128,plain,(
    ! [A_68,A_69] :
      ( k7_partfun1(A_68,'#skF_3',A_69) = k1_funct_1('#skF_3',A_69)
      | ~ v5_relat_1('#skF_3',A_68)
      | ~ m1_subset_1(A_69,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_124])).

tff(c_132,plain,(
    ! [A_70] :
      ( k7_partfun1('#skF_2','#skF_3',A_70) = k1_funct_1('#skF_3',A_70)
      | ~ m1_subset_1(A_70,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_75,c_128])).

tff(c_136,plain,(
    k7_partfun1('#skF_2','#skF_3','#skF_4') = k1_funct_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_132])).

tff(c_32,plain,(
    k3_funct_2('#skF_1','#skF_2','#skF_3','#skF_4') != k7_partfun1('#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_137,plain,(
    k3_funct_2('#skF_1','#skF_2','#skF_3','#skF_4') != k1_funct_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_32])).

tff(c_142,plain,(
    ! [A_71,B_72,C_73,D_74] :
      ( k3_funct_2(A_71,B_72,C_73,D_74) = k1_funct_1(C_73,D_74)
      | ~ m1_subset_1(D_74,A_71)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72)))
      | ~ v1_funct_2(C_73,A_71,B_72)
      | ~ v1_funct_1(C_73)
      | v1_xboole_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_146,plain,(
    ! [B_72,C_73] :
      ( k3_funct_2('#skF_1',B_72,C_73,'#skF_4') = k1_funct_1(C_73,'#skF_4')
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_72)))
      | ~ v1_funct_2(C_73,'#skF_1',B_72)
      | ~ v1_funct_1(C_73)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_34,c_142])).

tff(c_151,plain,(
    ! [B_75,C_76] :
      ( k3_funct_2('#skF_1',B_75,C_76,'#skF_4') = k1_funct_1(C_76,'#skF_4')
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_75)))
      | ~ v1_funct_2(C_76,'#skF_1',B_75)
      | ~ v1_funct_1(C_76) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_146])).

tff(c_154,plain,
    ( k3_funct_2('#skF_1','#skF_2','#skF_3','#skF_4') = k1_funct_1('#skF_3','#skF_4')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_151])).

tff(c_157,plain,(
    k3_funct_2('#skF_1','#skF_2','#skF_3','#skF_4') = k1_funct_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_154])).

tff(c_159,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_157])).

tff(c_160,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_101])).

tff(c_22,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_45,plain,(
    ! [A_35] :
      ( k1_xboole_0 = A_35
      | ~ v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_49,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_45])).

tff(c_50,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_22])).

tff(c_168,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_50])).

tff(c_172,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_168])).

%------------------------------------------------------------------------------
