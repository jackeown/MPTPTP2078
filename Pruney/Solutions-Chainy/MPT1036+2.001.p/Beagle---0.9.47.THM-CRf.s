%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:59 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 2.94s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 463 expanded)
%              Number of leaves         :   30 ( 175 expanded)
%              Depth                    :   13
%              Number of atoms          :  199 (1569 expanded)
%              Number of equality atoms :   57 ( 418 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_100,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & v1_funct_2(C,A,A)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( r1_partfun1(B,C)
            <=> ! [D] :
                  ( r2_hidden(D,k1_relset_1(A,A,B))
                 => k1_funct_1(B,D) = k1_funct_1(C,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_2)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_63,axiom,(
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

tff(f_81,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_partfun1)).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_53,plain,(
    ! [C_33,A_34,B_35] :
      ( v1_relat_1(C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_60,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_53])).

tff(c_305,plain,(
    ! [C_86,A_87,B_88] :
      ( v4_relat_1(C_86,A_87)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_312,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_305])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k1_relat_1(B_2),A_1)
      | ~ v4_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_42,plain,
    ( k1_funct_1('#skF_3','#skF_5') != k1_funct_1('#skF_4','#skF_5')
    | ~ r1_partfun1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_71,plain,(
    ~ r1_partfun1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_40,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_61,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_53])).

tff(c_36,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_78,plain,(
    ! [C_43,A_44,B_45] :
      ( v4_relat_1(C_43,A_44)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_85,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_78])).

tff(c_34,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_90,plain,(
    ! [A_48,B_49,C_50] :
      ( k1_relset_1(A_48,B_49,C_50) = k1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_98,plain,(
    k1_relset_1('#skF_2','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_90])).

tff(c_112,plain,(
    ! [B_58,A_59,C_60] :
      ( k1_xboole_0 = B_58
      | k1_relset_1(A_59,B_58,C_60) = A_59
      | ~ v1_funct_2(C_60,A_59,B_58)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_59,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_118,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_2','#skF_2','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_112])).

tff(c_123,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_98,c_118])).

tff(c_125,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_123])).

tff(c_171,plain,(
    ! [A_66,B_67] :
      ( r2_hidden('#skF_1'(A_66,B_67),k1_relat_1(A_66))
      | r1_partfun1(A_66,B_67)
      | ~ r1_tarski(k1_relat_1(A_66),k1_relat_1(B_67))
      | ~ v1_funct_1(B_67)
      | ~ v1_relat_1(B_67)
      | ~ v1_funct_1(A_66)
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_97,plain,(
    k1_relset_1('#skF_2','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_90])).

tff(c_52,plain,(
    ! [D_32] :
      ( r1_partfun1('#skF_3','#skF_4')
      | k1_funct_1('#skF_3',D_32) = k1_funct_1('#skF_4',D_32)
      | ~ r2_hidden(D_32,k1_relset_1('#skF_2','#skF_2','#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_87,plain,(
    ! [D_32] :
      ( k1_funct_1('#skF_3',D_32) = k1_funct_1('#skF_4',D_32)
      | ~ r2_hidden(D_32,k1_relset_1('#skF_2','#skF_2','#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_52])).

tff(c_99,plain,(
    ! [D_32] :
      ( k1_funct_1('#skF_3',D_32) = k1_funct_1('#skF_4',D_32)
      | ~ r2_hidden(D_32,k1_relat_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_87])).

tff(c_175,plain,(
    ! [B_67] :
      ( k1_funct_1('#skF_3','#skF_1'('#skF_3',B_67)) = k1_funct_1('#skF_4','#skF_1'('#skF_3',B_67))
      | r1_partfun1('#skF_3',B_67)
      | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1(B_67))
      | ~ v1_funct_1(B_67)
      | ~ v1_relat_1(B_67)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_171,c_99])).

tff(c_185,plain,(
    ! [B_69] :
      ( k1_funct_1('#skF_3','#skF_1'('#skF_3',B_69)) = k1_funct_1('#skF_4','#skF_1'('#skF_3',B_69))
      | r1_partfun1('#skF_3',B_69)
      | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1(B_69))
      | ~ v1_funct_1(B_69)
      | ~ v1_relat_1(B_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_40,c_175])).

tff(c_188,plain,
    ( k1_funct_1('#skF_3','#skF_1'('#skF_3','#skF_4')) = k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | r1_partfun1('#skF_3','#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_2')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_185])).

tff(c_193,plain,
    ( k1_funct_1('#skF_3','#skF_1'('#skF_3','#skF_4')) = k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | r1_partfun1('#skF_3','#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_36,c_188])).

tff(c_194,plain,
    ( k1_funct_1('#skF_3','#skF_1'('#skF_3','#skF_4')) = k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_193])).

tff(c_202,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_194])).

tff(c_205,plain,
    ( ~ v4_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_202])).

tff(c_209,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_85,c_205])).

tff(c_211,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_194])).

tff(c_210,plain,(
    k1_funct_1('#skF_3','#skF_1'('#skF_3','#skF_4')) = k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_194])).

tff(c_28,plain,(
    ! [B_21,A_15] :
      ( k1_funct_1(B_21,'#skF_1'(A_15,B_21)) != k1_funct_1(A_15,'#skF_1'(A_15,B_21))
      | r1_partfun1(A_15,B_21)
      | ~ r1_tarski(k1_relat_1(A_15),k1_relat_1(B_21))
      | ~ v1_funct_1(B_21)
      | ~ v1_relat_1(B_21)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_220,plain,
    ( r1_partfun1('#skF_3','#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_28])).

tff(c_225,plain,(
    r1_partfun1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_40,c_61,c_36,c_211,c_125,c_220])).

tff(c_227,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_225])).

tff(c_229,plain,(
    k1_relat_1('#skF_4') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_123])).

tff(c_228,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_123])).

tff(c_22,plain,(
    ! [B_13,C_14] :
      ( k1_relset_1(k1_xboole_0,B_13,C_14) = k1_xboole_0
      | ~ v1_funct_2(C_14,k1_xboole_0,B_13)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_280,plain,(
    ! [B_80,C_81] :
      ( k1_relset_1('#skF_2',B_80,C_81) = '#skF_2'
      | ~ v1_funct_2(C_81,'#skF_2',B_80)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_80))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_228,c_228,c_228,c_22])).

tff(c_286,plain,
    ( k1_relset_1('#skF_2','#skF_2','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_280])).

tff(c_292,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_98,c_286])).

tff(c_294,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_229,c_292])).

tff(c_295,plain,(
    k1_funct_1('#skF_3','#skF_5') != k1_funct_1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_296,plain,(
    r1_partfun1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_315,plain,(
    ! [A_89,B_90,C_91] :
      ( k1_relset_1(A_89,B_90,C_91) = k1_relat_1(C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_323,plain,(
    k1_relset_1('#skF_2','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_315])).

tff(c_338,plain,(
    ! [B_99,A_100,C_101] :
      ( k1_xboole_0 = B_99
      | k1_relset_1(A_100,B_99,C_101) = A_100
      | ~ v1_funct_2(C_101,A_100,B_99)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_100,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_344,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_2','#skF_2','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_338])).

tff(c_349,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_323,c_344])).

tff(c_350,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_349])).

tff(c_322,plain,(
    k1_relset_1('#skF_2','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_315])).

tff(c_44,plain,
    ( r2_hidden('#skF_5',k1_relset_1('#skF_2','#skF_2','#skF_3'))
    | ~ r1_partfun1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_299,plain,(
    r2_hidden('#skF_5',k1_relset_1('#skF_2','#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_296,c_44])).

tff(c_324,plain,(
    r2_hidden('#skF_5',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_299])).

tff(c_437,plain,(
    ! [B_114,C_115,A_116] :
      ( k1_funct_1(B_114,C_115) = k1_funct_1(A_116,C_115)
      | ~ r2_hidden(C_115,k1_relat_1(A_116))
      | ~ r1_partfun1(A_116,B_114)
      | ~ r1_tarski(k1_relat_1(A_116),k1_relat_1(B_114))
      | ~ v1_funct_1(B_114)
      | ~ v1_relat_1(B_114)
      | ~ v1_funct_1(A_116)
      | ~ v1_relat_1(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_443,plain,(
    ! [B_114] :
      ( k1_funct_1(B_114,'#skF_5') = k1_funct_1('#skF_3','#skF_5')
      | ~ r1_partfun1('#skF_3',B_114)
      | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1(B_114))
      | ~ v1_funct_1(B_114)
      | ~ v1_relat_1(B_114)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_324,c_437])).

tff(c_450,plain,(
    ! [B_117] :
      ( k1_funct_1(B_117,'#skF_5') = k1_funct_1('#skF_3','#skF_5')
      | ~ r1_partfun1('#skF_3',B_117)
      | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1(B_117))
      | ~ v1_funct_1(B_117)
      | ~ v1_relat_1(B_117) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_40,c_443])).

tff(c_453,plain,
    ( k1_funct_1('#skF_3','#skF_5') = k1_funct_1('#skF_4','#skF_5')
    | ~ r1_partfun1('#skF_3','#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_2')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_350,c_450])).

tff(c_458,plain,
    ( k1_funct_1('#skF_3','#skF_5') = k1_funct_1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_36,c_296,c_453])).

tff(c_459,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_295,c_458])).

tff(c_465,plain,
    ( ~ v4_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_459])).

tff(c_469,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_312,c_465])).

tff(c_471,plain,(
    k1_relat_1('#skF_4') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_349])).

tff(c_470,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_349])).

tff(c_523,plain,(
    ! [B_126,C_127] :
      ( k1_relset_1('#skF_2',B_126,C_127) = '#skF_2'
      | ~ v1_funct_2(C_127,'#skF_2',B_126)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_126))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_470,c_470,c_470,c_470,c_22])).

tff(c_529,plain,
    ( k1_relset_1('#skF_2','#skF_2','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_523])).

tff(c_535,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_323,c_529])).

tff(c_537,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_471,c_535])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:53:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.80/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/1.36  
% 2.94/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/1.36  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.94/1.36  
% 2.94/1.36  %Foreground sorts:
% 2.94/1.36  
% 2.94/1.36  
% 2.94/1.36  %Background operators:
% 2.94/1.36  
% 2.94/1.36  
% 2.94/1.36  %Foreground operators:
% 2.94/1.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.94/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.94/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.94/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.94/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.94/1.36  tff('#skF_5', type, '#skF_5': $i).
% 2.94/1.36  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.94/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.94/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.94/1.36  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.94/1.36  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.94/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.94/1.36  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.94/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.94/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.94/1.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.94/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.94/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.94/1.36  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.94/1.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.94/1.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.94/1.36  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 2.94/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.94/1.36  
% 2.94/1.38  tff(f_100, negated_conjecture, ~(![A, B]: ((v1_funct_1(B) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r1_partfun1(B, C) <=> (![D]: (r2_hidden(D, k1_relset_1(A, A, B)) => (k1_funct_1(B, D) = k1_funct_1(C, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_2)).
% 2.94/1.38  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.94/1.38  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.94/1.38  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.94/1.38  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.94/1.38  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.94/1.38  tff(f_81, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) => (r1_partfun1(A, B) <=> (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_partfun1)).
% 2.94/1.38  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.94/1.38  tff(c_53, plain, (![C_33, A_34, B_35]: (v1_relat_1(C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.94/1.38  tff(c_60, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_53])).
% 2.94/1.38  tff(c_305, plain, (![C_86, A_87, B_88]: (v4_relat_1(C_86, A_87) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.94/1.38  tff(c_312, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_305])).
% 2.94/1.38  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k1_relat_1(B_2), A_1) | ~v4_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.94/1.38  tff(c_42, plain, (k1_funct_1('#skF_3', '#skF_5')!=k1_funct_1('#skF_4', '#skF_5') | ~r1_partfun1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.94/1.38  tff(c_71, plain, (~r1_partfun1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_42])).
% 2.94/1.38  tff(c_40, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.94/1.38  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.94/1.38  tff(c_61, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_53])).
% 2.94/1.38  tff(c_36, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.94/1.38  tff(c_78, plain, (![C_43, A_44, B_45]: (v4_relat_1(C_43, A_44) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.94/1.38  tff(c_85, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_78])).
% 2.94/1.38  tff(c_34, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.94/1.38  tff(c_90, plain, (![A_48, B_49, C_50]: (k1_relset_1(A_48, B_49, C_50)=k1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.94/1.38  tff(c_98, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_90])).
% 2.94/1.38  tff(c_112, plain, (![B_58, A_59, C_60]: (k1_xboole_0=B_58 | k1_relset_1(A_59, B_58, C_60)=A_59 | ~v1_funct_2(C_60, A_59, B_58) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_59, B_58))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.94/1.38  tff(c_118, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_2', '#skF_2', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_112])).
% 2.94/1.38  tff(c_123, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_98, c_118])).
% 2.94/1.38  tff(c_125, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_123])).
% 2.94/1.38  tff(c_171, plain, (![A_66, B_67]: (r2_hidden('#skF_1'(A_66, B_67), k1_relat_1(A_66)) | r1_partfun1(A_66, B_67) | ~r1_tarski(k1_relat_1(A_66), k1_relat_1(B_67)) | ~v1_funct_1(B_67) | ~v1_relat_1(B_67) | ~v1_funct_1(A_66) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.94/1.38  tff(c_97, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_90])).
% 2.94/1.38  tff(c_52, plain, (![D_32]: (r1_partfun1('#skF_3', '#skF_4') | k1_funct_1('#skF_3', D_32)=k1_funct_1('#skF_4', D_32) | ~r2_hidden(D_32, k1_relset_1('#skF_2', '#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.94/1.38  tff(c_87, plain, (![D_32]: (k1_funct_1('#skF_3', D_32)=k1_funct_1('#skF_4', D_32) | ~r2_hidden(D_32, k1_relset_1('#skF_2', '#skF_2', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_71, c_52])).
% 2.94/1.38  tff(c_99, plain, (![D_32]: (k1_funct_1('#skF_3', D_32)=k1_funct_1('#skF_4', D_32) | ~r2_hidden(D_32, k1_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_87])).
% 2.94/1.38  tff(c_175, plain, (![B_67]: (k1_funct_1('#skF_3', '#skF_1'('#skF_3', B_67))=k1_funct_1('#skF_4', '#skF_1'('#skF_3', B_67)) | r1_partfun1('#skF_3', B_67) | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1(B_67)) | ~v1_funct_1(B_67) | ~v1_relat_1(B_67) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_171, c_99])).
% 2.94/1.38  tff(c_185, plain, (![B_69]: (k1_funct_1('#skF_3', '#skF_1'('#skF_3', B_69))=k1_funct_1('#skF_4', '#skF_1'('#skF_3', B_69)) | r1_partfun1('#skF_3', B_69) | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1(B_69)) | ~v1_funct_1(B_69) | ~v1_relat_1(B_69))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_40, c_175])).
% 2.94/1.38  tff(c_188, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_3', '#skF_4'))=k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | r1_partfun1('#skF_3', '#skF_4') | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_2') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_125, c_185])).
% 2.94/1.38  tff(c_193, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_3', '#skF_4'))=k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | r1_partfun1('#skF_3', '#skF_4') | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_61, c_36, c_188])).
% 2.94/1.38  tff(c_194, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_3', '#skF_4'))=k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_71, c_193])).
% 2.94/1.38  tff(c_202, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_194])).
% 2.94/1.38  tff(c_205, plain, (~v4_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4, c_202])).
% 2.94/1.38  tff(c_209, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_85, c_205])).
% 2.94/1.38  tff(c_211, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_194])).
% 2.94/1.38  tff(c_210, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_3', '#skF_4'))=k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_194])).
% 2.94/1.38  tff(c_28, plain, (![B_21, A_15]: (k1_funct_1(B_21, '#skF_1'(A_15, B_21))!=k1_funct_1(A_15, '#skF_1'(A_15, B_21)) | r1_partfun1(A_15, B_21) | ~r1_tarski(k1_relat_1(A_15), k1_relat_1(B_21)) | ~v1_funct_1(B_21) | ~v1_relat_1(B_21) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.94/1.38  tff(c_220, plain, (r1_partfun1('#skF_3', '#skF_4') | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_210, c_28])).
% 2.94/1.38  tff(c_225, plain, (r1_partfun1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_40, c_61, c_36, c_211, c_125, c_220])).
% 2.94/1.38  tff(c_227, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_225])).
% 2.94/1.38  tff(c_229, plain, (k1_relat_1('#skF_4')!='#skF_2'), inference(splitRight, [status(thm)], [c_123])).
% 2.94/1.38  tff(c_228, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_123])).
% 2.94/1.38  tff(c_22, plain, (![B_13, C_14]: (k1_relset_1(k1_xboole_0, B_13, C_14)=k1_xboole_0 | ~v1_funct_2(C_14, k1_xboole_0, B_13) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_13))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.94/1.38  tff(c_280, plain, (![B_80, C_81]: (k1_relset_1('#skF_2', B_80, C_81)='#skF_2' | ~v1_funct_2(C_81, '#skF_2', B_80) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_80))))), inference(demodulation, [status(thm), theory('equality')], [c_228, c_228, c_228, c_228, c_22])).
% 2.94/1.38  tff(c_286, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_280])).
% 2.94/1.38  tff(c_292, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_98, c_286])).
% 2.94/1.38  tff(c_294, plain, $false, inference(negUnitSimplification, [status(thm)], [c_229, c_292])).
% 2.94/1.38  tff(c_295, plain, (k1_funct_1('#skF_3', '#skF_5')!=k1_funct_1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_42])).
% 2.94/1.38  tff(c_296, plain, (r1_partfun1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_42])).
% 2.94/1.38  tff(c_315, plain, (![A_89, B_90, C_91]: (k1_relset_1(A_89, B_90, C_91)=k1_relat_1(C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.94/1.38  tff(c_323, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_315])).
% 2.94/1.38  tff(c_338, plain, (![B_99, A_100, C_101]: (k1_xboole_0=B_99 | k1_relset_1(A_100, B_99, C_101)=A_100 | ~v1_funct_2(C_101, A_100, B_99) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_100, B_99))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.94/1.38  tff(c_344, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_2', '#skF_2', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_338])).
% 2.94/1.38  tff(c_349, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_323, c_344])).
% 2.94/1.38  tff(c_350, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_349])).
% 2.94/1.38  tff(c_322, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_315])).
% 2.94/1.38  tff(c_44, plain, (r2_hidden('#skF_5', k1_relset_1('#skF_2', '#skF_2', '#skF_3')) | ~r1_partfun1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.94/1.38  tff(c_299, plain, (r2_hidden('#skF_5', k1_relset_1('#skF_2', '#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_296, c_44])).
% 2.94/1.38  tff(c_324, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_322, c_299])).
% 2.94/1.38  tff(c_437, plain, (![B_114, C_115, A_116]: (k1_funct_1(B_114, C_115)=k1_funct_1(A_116, C_115) | ~r2_hidden(C_115, k1_relat_1(A_116)) | ~r1_partfun1(A_116, B_114) | ~r1_tarski(k1_relat_1(A_116), k1_relat_1(B_114)) | ~v1_funct_1(B_114) | ~v1_relat_1(B_114) | ~v1_funct_1(A_116) | ~v1_relat_1(A_116))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.94/1.38  tff(c_443, plain, (![B_114]: (k1_funct_1(B_114, '#skF_5')=k1_funct_1('#skF_3', '#skF_5') | ~r1_partfun1('#skF_3', B_114) | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1(B_114)) | ~v1_funct_1(B_114) | ~v1_relat_1(B_114) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_324, c_437])).
% 2.94/1.38  tff(c_450, plain, (![B_117]: (k1_funct_1(B_117, '#skF_5')=k1_funct_1('#skF_3', '#skF_5') | ~r1_partfun1('#skF_3', B_117) | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1(B_117)) | ~v1_funct_1(B_117) | ~v1_relat_1(B_117))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_40, c_443])).
% 2.94/1.38  tff(c_453, plain, (k1_funct_1('#skF_3', '#skF_5')=k1_funct_1('#skF_4', '#skF_5') | ~r1_partfun1('#skF_3', '#skF_4') | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_2') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_350, c_450])).
% 2.94/1.38  tff(c_458, plain, (k1_funct_1('#skF_3', '#skF_5')=k1_funct_1('#skF_4', '#skF_5') | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_61, c_36, c_296, c_453])).
% 2.94/1.38  tff(c_459, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_295, c_458])).
% 2.94/1.38  tff(c_465, plain, (~v4_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4, c_459])).
% 2.94/1.38  tff(c_469, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_312, c_465])).
% 2.94/1.38  tff(c_471, plain, (k1_relat_1('#skF_4')!='#skF_2'), inference(splitRight, [status(thm)], [c_349])).
% 2.94/1.38  tff(c_470, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_349])).
% 2.94/1.38  tff(c_523, plain, (![B_126, C_127]: (k1_relset_1('#skF_2', B_126, C_127)='#skF_2' | ~v1_funct_2(C_127, '#skF_2', B_126) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_126))))), inference(demodulation, [status(thm), theory('equality')], [c_470, c_470, c_470, c_470, c_22])).
% 2.94/1.38  tff(c_529, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_523])).
% 2.94/1.38  tff(c_535, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_323, c_529])).
% 2.94/1.38  tff(c_537, plain, $false, inference(negUnitSimplification, [status(thm)], [c_471, c_535])).
% 2.94/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/1.38  
% 2.94/1.38  Inference rules
% 2.94/1.38  ----------------------
% 2.94/1.38  #Ref     : 2
% 2.94/1.38  #Sup     : 87
% 2.94/1.38  #Fact    : 0
% 2.94/1.38  #Define  : 0
% 2.94/1.38  #Split   : 10
% 2.94/1.38  #Chain   : 0
% 2.94/1.38  #Close   : 0
% 2.94/1.38  
% 2.94/1.38  Ordering : KBO
% 2.94/1.38  
% 2.94/1.38  Simplification rules
% 2.94/1.38  ----------------------
% 2.94/1.38  #Subsume      : 8
% 2.94/1.38  #Demod        : 148
% 2.94/1.38  #Tautology    : 44
% 2.94/1.38  #SimpNegUnit  : 10
% 2.94/1.38  #BackRed      : 14
% 2.94/1.38  
% 2.94/1.38  #Partial instantiations: 0
% 2.94/1.38  #Strategies tried      : 1
% 2.94/1.38  
% 2.94/1.38  Timing (in seconds)
% 2.94/1.38  ----------------------
% 2.94/1.39  Preprocessing        : 0.33
% 2.94/1.39  Parsing              : 0.16
% 2.94/1.39  CNF conversion       : 0.02
% 2.94/1.39  Main loop            : 0.33
% 2.94/1.39  Inferencing          : 0.12
% 2.94/1.39  Reduction            : 0.10
% 2.94/1.39  Demodulation         : 0.07
% 2.94/1.39  BG Simplification    : 0.02
% 2.94/1.39  Subsumption          : 0.05
% 2.94/1.39  Abstraction          : 0.01
% 2.94/1.39  MUC search           : 0.00
% 2.94/1.39  Cooper               : 0.00
% 2.94/1.39  Total                : 0.71
% 2.94/1.39  Index Insertion      : 0.00
% 2.94/1.39  Index Deletion       : 0.00
% 2.94/1.39  Index Matching       : 0.00
% 2.94/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
