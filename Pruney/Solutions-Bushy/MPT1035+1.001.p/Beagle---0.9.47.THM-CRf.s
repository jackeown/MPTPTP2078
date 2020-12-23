%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1035+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:17 EST 2020

% Result     : Theorem 4.03s
% Output     : CNFRefutation 4.03s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 669 expanded)
%              Number of leaves         :   29 ( 223 expanded)
%              Depth                    :   15
%              Number of atoms          :  310 (2408 expanded)
%              Number of equality atoms :   81 ( 858 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_99,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( ( B = k1_xboole_0
               => A = k1_xboole_0 )
             => ( r1_partfun1(C,D)
              <=> ! [E] :
                    ( r2_hidden(E,k1_relset_1(A,B,C))
                   => k1_funct_1(C,E) = k1_funct_1(D,E) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_2)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_46,axiom,(
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

tff(f_72,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
           => ( r1_partfun1(A,B)
            <=> ! [C] :
                  ( r2_hidden(C,k1_relat_1(A))
                 => k1_funct_1(A,C) = k1_funct_1(B,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_partfun1)).

tff(c_44,plain,
    ( r2_hidden('#skF_6',k1_relset_1('#skF_2','#skF_3','#skF_4'))
    | ~ r1_partfun1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_63,plain,(
    ~ r1_partfun1('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_69,plain,(
    ! [C_37,A_38,B_39] :
      ( v1_relat_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_81,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_69])).

tff(c_40,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_82,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_69])).

tff(c_36,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_102,plain,(
    ! [A_46,B_47,C_48] :
      ( k1_relset_1(A_46,B_47,C_48) = k1_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_114,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_102])).

tff(c_126,plain,(
    ! [A_50,B_51,C_52] :
      ( m1_subset_1(k1_relset_1(A_50,B_51,C_52),k1_zfmisc_1(A_50))
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_143,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_126])).

tff(c_150,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_143])).

tff(c_26,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(A_23,B_24)
      | ~ m1_subset_1(A_23,k1_zfmisc_1(B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_158,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_150,c_26])).

tff(c_30,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_53,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_34,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_115,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_102])).

tff(c_278,plain,(
    ! [B_82,A_83,C_84] :
      ( k1_xboole_0 = B_82
      | k1_relset_1(A_83,B_82,C_84) = A_83
      | ~ v1_funct_2(C_84,A_83,B_82)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_83,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_292,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_278])).

tff(c_300,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_115,c_292])).

tff(c_301,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_300])).

tff(c_432,plain,(
    ! [A_98,B_99] :
      ( r2_hidden('#skF_1'(A_98,B_99),k1_relat_1(A_98))
      | r1_partfun1(A_98,B_99)
      | ~ r1_tarski(k1_relat_1(A_98),k1_relat_1(B_99))
      | ~ v1_funct_1(B_99)
      | ~ v1_relat_1(B_99)
      | ~ v1_funct_1(A_98)
      | ~ v1_relat_1(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_52,plain,(
    ! [E_32] :
      ( r1_partfun1('#skF_4','#skF_5')
      | k1_funct_1('#skF_5',E_32) = k1_funct_1('#skF_4',E_32)
      | ~ r2_hidden(E_32,k1_relset_1('#skF_2','#skF_3','#skF_4')) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_99,plain,(
    ! [E_32] :
      ( k1_funct_1('#skF_5',E_32) = k1_funct_1('#skF_4',E_32)
      | ~ r2_hidden(E_32,k1_relset_1('#skF_2','#skF_3','#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_52])).

tff(c_116,plain,(
    ! [E_32] :
      ( k1_funct_1('#skF_5',E_32) = k1_funct_1('#skF_4',E_32)
      | ~ r2_hidden(E_32,k1_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_99])).

tff(c_436,plain,(
    ! [B_99] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_99)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_99))
      | r1_partfun1('#skF_4',B_99)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_99))
      | ~ v1_funct_1(B_99)
      | ~ v1_relat_1(B_99)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_432,c_116])).

tff(c_446,plain,(
    ! [B_101] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_101)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_101))
      | r1_partfun1('#skF_4',B_101)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_101))
      | ~ v1_funct_1(B_101)
      | ~ v1_relat_1(B_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_40,c_436])).

tff(c_449,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_5'))
    | r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_446])).

tff(c_451,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_5'))
    | r1_partfun1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_36,c_158,c_449])).

tff(c_452,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_451])).

tff(c_492,plain,(
    ! [B_125,A_126] :
      ( k1_funct_1(B_125,'#skF_1'(A_126,B_125)) != k1_funct_1(A_126,'#skF_1'(A_126,B_125))
      | r1_partfun1(A_126,B_125)
      | ~ r1_tarski(k1_relat_1(A_126),k1_relat_1(B_125))
      | ~ v1_funct_1(B_125)
      | ~ v1_relat_1(B_125)
      | ~ v1_funct_1(A_126)
      | ~ v1_relat_1(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_494,plain,
    ( r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_452,c_492])).

tff(c_497,plain,(
    r1_partfun1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_40,c_82,c_36,c_158,c_301,c_494])).

tff(c_499,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_497])).

tff(c_501,plain,(
    r1_partfun1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_42,plain,
    ( k1_funct_1('#skF_5','#skF_6') != k1_funct_1('#skF_4','#skF_6')
    | ~ r1_partfun1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_503,plain,(
    k1_funct_1('#skF_5','#skF_6') != k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_501,c_42])).

tff(c_509,plain,(
    ! [C_129,A_130,B_131] :
      ( v1_relat_1(C_129)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(A_130,B_131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_522,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_509])).

tff(c_540,plain,(
    ! [A_137,B_138,C_139] :
      ( k1_relset_1(A_137,B_138,C_139) = k1_relat_1(C_139)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_137,B_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_552,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_540])).

tff(c_575,plain,(
    ! [A_143,B_144,C_145] :
      ( m1_subset_1(k1_relset_1(A_143,B_144,C_145),k1_zfmisc_1(A_143))
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(A_143,B_144))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_592,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_552,c_575])).

tff(c_599,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_592])).

tff(c_618,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_599,c_26])).

tff(c_553,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_540])).

tff(c_716,plain,(
    ! [B_172,A_173,C_174] :
      ( k1_xboole_0 = B_172
      | k1_relset_1(A_173,B_172,C_174) = A_173
      | ~ v1_funct_2(C_174,A_173,B_172)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(A_173,B_172))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_730,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_716])).

tff(c_738,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_553,c_730])).

tff(c_739,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_738])).

tff(c_521,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_509])).

tff(c_500,plain,(
    r2_hidden('#skF_6',k1_relset_1('#skF_2','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_554,plain,(
    r2_hidden('#skF_6',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_552,c_500])).

tff(c_903,plain,(
    ! [B_198,C_199,A_200] :
      ( k1_funct_1(B_198,C_199) = k1_funct_1(A_200,C_199)
      | ~ r2_hidden(C_199,k1_relat_1(A_200))
      | ~ r1_partfun1(A_200,B_198)
      | ~ r1_tarski(k1_relat_1(A_200),k1_relat_1(B_198))
      | ~ v1_funct_1(B_198)
      | ~ v1_relat_1(B_198)
      | ~ v1_funct_1(A_200)
      | ~ v1_relat_1(A_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_909,plain,(
    ! [B_198] :
      ( k1_funct_1(B_198,'#skF_6') = k1_funct_1('#skF_4','#skF_6')
      | ~ r1_partfun1('#skF_4',B_198)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_198))
      | ~ v1_funct_1(B_198)
      | ~ v1_relat_1(B_198)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_554,c_903])).

tff(c_916,plain,(
    ! [B_201] :
      ( k1_funct_1(B_201,'#skF_6') = k1_funct_1('#skF_4','#skF_6')
      | ~ r1_partfun1('#skF_4',B_201)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_201))
      | ~ v1_funct_1(B_201)
      | ~ v1_relat_1(B_201) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_521,c_40,c_909])).

tff(c_919,plain,
    ( k1_funct_1('#skF_5','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_739,c_916])).

tff(c_921,plain,(
    k1_funct_1('#skF_5','#skF_6') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_522,c_36,c_618,c_501,c_919])).

tff(c_923,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_503,c_921])).

tff(c_925,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_924,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_930,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_925,c_924])).

tff(c_951,plain,
    ( r2_hidden('#skF_6',k1_relset_1('#skF_3','#skF_3','#skF_4'))
    | ~ r1_partfun1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_930,c_44])).

tff(c_952,plain,(
    ~ r1_partfun1('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_951])).

tff(c_941,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_930,c_38])).

tff(c_958,plain,(
    ! [C_206,A_207,B_208] :
      ( v1_relat_1(C_206)
      | ~ m1_subset_1(C_206,k1_zfmisc_1(k2_zfmisc_1(A_207,B_208))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_970,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_941,c_958])).

tff(c_940,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_930,c_32])).

tff(c_971,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_940,c_958])).

tff(c_993,plain,(
    ! [A_215,B_216,C_217] :
      ( k1_relset_1(A_215,B_216,C_217) = k1_relat_1(C_217)
      | ~ m1_subset_1(C_217,k1_zfmisc_1(k2_zfmisc_1(A_215,B_216))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1005,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_941,c_993])).

tff(c_1017,plain,(
    ! [A_219,B_220,C_221] :
      ( m1_subset_1(k1_relset_1(A_219,B_220,C_221),k1_zfmisc_1(A_219))
      | ~ m1_subset_1(C_221,k1_zfmisc_1(k2_zfmisc_1(A_219,B_220))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1034,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1005,c_1017])).

tff(c_1041,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_941,c_1034])).

tff(c_1049,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1041,c_26])).

tff(c_935,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_930,c_34])).

tff(c_1006,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_940,c_993])).

tff(c_12,plain,(
    ! [B_5,C_6] :
      ( k1_relset_1(k1_xboole_0,B_5,C_6) = k1_xboole_0
      | ~ v1_funct_2(C_6,k1_xboole_0,B_5)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_5))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1125,plain,(
    ! [B_233,C_234] :
      ( k1_relset_1('#skF_3',B_233,C_234) = '#skF_3'
      | ~ v1_funct_2(C_234,'#skF_3',B_233)
      | ~ m1_subset_1(C_234,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_233))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_925,c_925,c_925,c_925,c_12])).

tff(c_1139,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_940,c_1125])).

tff(c_1146,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_935,c_1006,c_1139])).

tff(c_1397,plain,(
    ! [A_267,B_268] :
      ( r2_hidden('#skF_1'(A_267,B_268),k1_relat_1(A_267))
      | r1_partfun1(A_267,B_268)
      | ~ r1_tarski(k1_relat_1(A_267),k1_relat_1(B_268))
      | ~ v1_funct_1(B_268)
      | ~ v1_relat_1(B_268)
      | ~ v1_funct_1(A_267)
      | ~ v1_relat_1(A_267) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_989,plain,(
    ! [E_32] :
      ( r1_partfun1('#skF_4','#skF_5')
      | k1_funct_1('#skF_5',E_32) = k1_funct_1('#skF_4',E_32)
      | ~ r2_hidden(E_32,k1_relset_1('#skF_3','#skF_3','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_930,c_52])).

tff(c_990,plain,(
    ! [E_32] :
      ( k1_funct_1('#skF_5',E_32) = k1_funct_1('#skF_4',E_32)
      | ~ r2_hidden(E_32,k1_relset_1('#skF_3','#skF_3','#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_952,c_989])).

tff(c_1007,plain,(
    ! [E_32] :
      ( k1_funct_1('#skF_5',E_32) = k1_funct_1('#skF_4',E_32)
      | ~ r2_hidden(E_32,k1_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1005,c_990])).

tff(c_1401,plain,(
    ! [B_268] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_268)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_268))
      | r1_partfun1('#skF_4',B_268)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_268))
      | ~ v1_funct_1(B_268)
      | ~ v1_relat_1(B_268)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1397,c_1007])).

tff(c_1411,plain,(
    ! [B_270] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_270)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_270))
      | r1_partfun1('#skF_4',B_270)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_270))
      | ~ v1_funct_1(B_270)
      | ~ v1_relat_1(B_270) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_970,c_40,c_1401])).

tff(c_1414,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_5'))
    | r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1146,c_1411])).

tff(c_1416,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_5'))
    | r1_partfun1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_971,c_36,c_1049,c_1414])).

tff(c_1417,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_952,c_1416])).

tff(c_1457,plain,(
    ! [B_294,A_295] :
      ( k1_funct_1(B_294,'#skF_1'(A_295,B_294)) != k1_funct_1(A_295,'#skF_1'(A_295,B_294))
      | r1_partfun1(A_295,B_294)
      | ~ r1_tarski(k1_relat_1(A_295),k1_relat_1(B_294))
      | ~ v1_funct_1(B_294)
      | ~ v1_relat_1(B_294)
      | ~ v1_funct_1(A_295)
      | ~ v1_relat_1(A_295) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1459,plain,
    ( r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1417,c_1457])).

tff(c_1462,plain,(
    r1_partfun1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_970,c_40,c_971,c_36,c_1049,c_1146,c_1459])).

tff(c_1464,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_952,c_1462])).

tff(c_1466,plain,(
    r1_partfun1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_951])).

tff(c_1468,plain,(
    k1_funct_1('#skF_5','#skF_6') != k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1466,c_42])).

tff(c_1474,plain,(
    ! [C_298,A_299,B_300] :
      ( v1_relat_1(C_298)
      | ~ m1_subset_1(C_298,k1_zfmisc_1(k2_zfmisc_1(A_299,B_300))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_1487,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_940,c_1474])).

tff(c_1506,plain,(
    ! [A_306,B_307,C_308] :
      ( k1_relset_1(A_306,B_307,C_308) = k1_relat_1(C_308)
      | ~ m1_subset_1(C_308,k1_zfmisc_1(k2_zfmisc_1(A_306,B_307))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1518,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_941,c_1506])).

tff(c_1541,plain,(
    ! [A_312,B_313,C_314] :
      ( m1_subset_1(k1_relset_1(A_312,B_313,C_314),k1_zfmisc_1(A_312))
      | ~ m1_subset_1(C_314,k1_zfmisc_1(k2_zfmisc_1(A_312,B_313))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1558,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1518,c_1541])).

tff(c_1565,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_941,c_1558])).

tff(c_1597,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1565,c_26])).

tff(c_1519,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_940,c_1506])).

tff(c_1662,plain,(
    ! [B_329,C_330] :
      ( k1_relset_1('#skF_3',B_329,C_330) = '#skF_3'
      | ~ v1_funct_2(C_330,'#skF_3',B_329)
      | ~ m1_subset_1(C_330,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_329))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_925,c_925,c_925,c_925,c_12])).

tff(c_1676,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_940,c_1662])).

tff(c_1683,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_935,c_1519,c_1676])).

tff(c_1486,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_941,c_1474])).

tff(c_1465,plain,(
    r2_hidden('#skF_6',k1_relset_1('#skF_3','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_951])).

tff(c_1520,plain,(
    r2_hidden('#skF_6',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1518,c_1465])).

tff(c_1943,plain,(
    ! [B_367,C_368,A_369] :
      ( k1_funct_1(B_367,C_368) = k1_funct_1(A_369,C_368)
      | ~ r2_hidden(C_368,k1_relat_1(A_369))
      | ~ r1_partfun1(A_369,B_367)
      | ~ r1_tarski(k1_relat_1(A_369),k1_relat_1(B_367))
      | ~ v1_funct_1(B_367)
      | ~ v1_relat_1(B_367)
      | ~ v1_funct_1(A_369)
      | ~ v1_relat_1(A_369) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1949,plain,(
    ! [B_367] :
      ( k1_funct_1(B_367,'#skF_6') = k1_funct_1('#skF_4','#skF_6')
      | ~ r1_partfun1('#skF_4',B_367)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_367))
      | ~ v1_funct_1(B_367)
      | ~ v1_relat_1(B_367)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1520,c_1943])).

tff(c_1956,plain,(
    ! [B_370] :
      ( k1_funct_1(B_370,'#skF_6') = k1_funct_1('#skF_4','#skF_6')
      | ~ r1_partfun1('#skF_4',B_370)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_370))
      | ~ v1_funct_1(B_370)
      | ~ v1_relat_1(B_370) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1486,c_40,c_1949])).

tff(c_1959,plain,
    ( k1_funct_1('#skF_5','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1683,c_1956])).

tff(c_1961,plain,(
    k1_funct_1('#skF_5','#skF_6') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1487,c_36,c_1597,c_1466,c_1959])).

tff(c_1963,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1468,c_1961])).

%------------------------------------------------------------------------------
