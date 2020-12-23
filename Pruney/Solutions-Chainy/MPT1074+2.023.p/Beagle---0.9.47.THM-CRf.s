%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:09 EST 2020

% Result     : Theorem 3.36s
% Output     : CNFRefutation 3.52s
% Verified   : 
% Statistics : Number of formulae       :  110 (1049 expanded)
%              Number of leaves         :   36 ( 381 expanded)
%              Depth                    :   25
%              Number of atoms          :  211 (3640 expanded)
%              Number of equality atoms :   37 ( 734 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_125,negated_conjecture,(
    ~ ! [A,B] :
        ( ~ v1_xboole_0(B)
       => ! [C] :
            ( ~ v1_xboole_0(C)
           => ! [D] :
                ( ( v1_funct_1(D)
                  & v1_funct_2(D,B,C)
                  & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
               => ( ! [E] :
                      ( m1_subset_1(E,B)
                     => r2_hidden(k3_funct_2(B,C,D,E),A) )
                 => r1_tarski(k2_relset_1(B,C,D),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_funct_2)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_43,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_73,axiom,(
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

tff(f_103,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( k1_relat_1(C) = A
          & ! [D] :
              ( r2_hidden(D,A)
             => r2_hidden(k1_funct_1(C,D),B) ) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_86,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_56,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_121,plain,(
    ! [A_64,B_65,C_66] :
      ( k2_relset_1(A_64,B_65,C_66) = k2_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_130,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_121])).

tff(c_46,plain,(
    ~ r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_131,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_46])).

tff(c_54,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_52,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_58,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_12,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_76,plain,(
    ! [B_51,A_52] :
      ( v1_relat_1(B_51)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_52))
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_82,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_50,c_76])).

tff(c_86,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_82])).

tff(c_101,plain,(
    ! [A_58,B_59,C_60] :
      ( k1_relset_1(A_58,B_59,C_60) = k1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_110,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_101])).

tff(c_290,plain,(
    ! [B_97,A_98,C_99] :
      ( k1_xboole_0 = B_97
      | k1_relset_1(A_98,B_97,C_99) = A_98
      | ~ v1_funct_2(C_99,A_98,B_97)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_98,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_301,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_290])).

tff(c_306,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_110,c_301])).

tff(c_307,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_306])).

tff(c_313,plain,(
    ! [C_100,B_101] :
      ( r2_hidden('#skF_1'(k1_relat_1(C_100),B_101,C_100),k1_relat_1(C_100))
      | v1_funct_2(C_100,k1_relat_1(C_100),B_101)
      | ~ v1_funct_1(C_100)
      | ~ v1_relat_1(C_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_319,plain,(
    ! [B_101] :
      ( r2_hidden('#skF_1'('#skF_3',B_101,'#skF_5'),k1_relat_1('#skF_5'))
      | v1_funct_2('#skF_5',k1_relat_1('#skF_5'),B_101)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_313])).

tff(c_332,plain,(
    ! [B_102] :
      ( r2_hidden('#skF_1'('#skF_3',B_102,'#skF_5'),'#skF_3')
      | v1_funct_2('#skF_5','#skF_3',B_102) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_54,c_307,c_307,c_319])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_336,plain,(
    ! [B_102] :
      ( m1_subset_1('#skF_1'('#skF_3',B_102,'#skF_5'),'#skF_3')
      | v1_funct_2('#skF_5','#skF_3',B_102) ) ),
    inference(resolution,[status(thm)],[c_332,c_4])).

tff(c_614,plain,(
    ! [A_134,B_135,C_136,D_137] :
      ( k3_funct_2(A_134,B_135,C_136,D_137) = k1_funct_1(C_136,D_137)
      | ~ m1_subset_1(D_137,A_134)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135)))
      | ~ v1_funct_2(C_136,A_134,B_135)
      | ~ v1_funct_1(C_136)
      | v1_xboole_0(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_626,plain,(
    ! [B_135,C_136,B_102] :
      ( k3_funct_2('#skF_3',B_135,C_136,'#skF_1'('#skF_3',B_102,'#skF_5')) = k1_funct_1(C_136,'#skF_1'('#skF_3',B_102,'#skF_5'))
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_135)))
      | ~ v1_funct_2(C_136,'#skF_3',B_135)
      | ~ v1_funct_1(C_136)
      | v1_xboole_0('#skF_3')
      | v1_funct_2('#skF_5','#skF_3',B_102) ) ),
    inference(resolution,[status(thm)],[c_336,c_614])).

tff(c_657,plain,(
    ! [B_138,C_139,B_140] :
      ( k3_funct_2('#skF_3',B_138,C_139,'#skF_1'('#skF_3',B_140,'#skF_5')) = k1_funct_1(C_139,'#skF_1'('#skF_3',B_140,'#skF_5'))
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_138)))
      | ~ v1_funct_2(C_139,'#skF_3',B_138)
      | ~ v1_funct_1(C_139)
      | v1_funct_2('#skF_5','#skF_3',B_140) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_626])).

tff(c_667,plain,(
    ! [B_140] :
      ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'('#skF_3',B_140,'#skF_5')) = k1_funct_1('#skF_5','#skF_1'('#skF_3',B_140,'#skF_5'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5')
      | v1_funct_2('#skF_5','#skF_3',B_140) ) ),
    inference(resolution,[status(thm)],[c_50,c_657])).

tff(c_676,plain,(
    ! [B_141] :
      ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'('#skF_3',B_141,'#skF_5')) = k1_funct_1('#skF_5','#skF_1'('#skF_3',B_141,'#skF_5'))
      | v1_funct_2('#skF_5','#skF_3',B_141) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_667])).

tff(c_48,plain,(
    ! [E_41] :
      ( r2_hidden(k3_funct_2('#skF_3','#skF_4','#skF_5',E_41),'#skF_2')
      | ~ m1_subset_1(E_41,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_695,plain,(
    ! [B_143] :
      ( r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_143,'#skF_5')),'#skF_2')
      | ~ m1_subset_1('#skF_1'('#skF_3',B_143,'#skF_5'),'#skF_3')
      | v1_funct_2('#skF_5','#skF_3',B_143) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_676,c_48])).

tff(c_390,plain,(
    ! [C_115,B_116] :
      ( ~ r2_hidden(k1_funct_1(C_115,'#skF_1'(k1_relat_1(C_115),B_116,C_115)),B_116)
      | v1_funct_2(C_115,k1_relat_1(C_115),B_116)
      | ~ v1_funct_1(C_115)
      | ~ v1_relat_1(C_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_393,plain,(
    ! [B_116] :
      ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_116,'#skF_5')),B_116)
      | v1_funct_2('#skF_5',k1_relat_1('#skF_5'),B_116)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_390])).

tff(c_395,plain,(
    ! [B_116] :
      ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_116,'#skF_5')),B_116)
      | v1_funct_2('#skF_5','#skF_3',B_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_54,c_307,c_393])).

tff(c_708,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3')
    | v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_695,c_395])).

tff(c_710,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_708])).

tff(c_396,plain,(
    ! [C_117,B_118] :
      ( r2_hidden('#skF_1'(k1_relat_1(C_117),B_118,C_117),k1_relat_1(C_117))
      | m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_117),B_118)))
      | ~ v1_funct_1(C_117)
      | ~ v1_relat_1(C_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_402,plain,(
    ! [B_118] :
      ( r2_hidden('#skF_1'('#skF_3',B_118,'#skF_5'),k1_relat_1('#skF_5'))
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),B_118)))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_396])).

tff(c_412,plain,(
    ! [B_120] :
      ( r2_hidden('#skF_1'('#skF_3',B_120,'#skF_5'),'#skF_3')
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_120))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_54,c_307,c_307,c_402])).

tff(c_18,plain,(
    ! [A_16,B_17,C_18] :
      ( k2_relset_1(A_16,B_17,C_18) = k2_relat_1(C_18)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_496,plain,(
    ! [B_125] :
      ( k2_relset_1('#skF_3',B_125,'#skF_5') = k2_relat_1('#skF_5')
      | r2_hidden('#skF_1'('#skF_3',B_125,'#skF_5'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_412,c_18])).

tff(c_500,plain,(
    ! [B_125] :
      ( m1_subset_1('#skF_1'('#skF_3',B_125,'#skF_5'),'#skF_3')
      | k2_relset_1('#skF_3',B_125,'#skF_5') = k2_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_496,c_4])).

tff(c_738,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_500,c_710])).

tff(c_136,plain,(
    ! [A_67,B_68,C_69] :
      ( m1_subset_1(k2_relset_1(A_67,B_68,C_69),k1_zfmisc_1(B_68))
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_157,plain,(
    ! [A_67,B_68,C_69] :
      ( r1_tarski(k2_relset_1(A_67,B_68,C_69),B_68)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(resolution,[status(thm)],[c_136,c_6])).

tff(c_501,plain,(
    ! [B_126] :
      ( r1_tarski(k2_relset_1('#skF_3',B_126,'#skF_5'),B_126)
      | r2_hidden('#skF_1'('#skF_3',B_126,'#skF_5'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_412,c_157])).

tff(c_550,plain,(
    ! [B_126] :
      ( m1_subset_1('#skF_1'('#skF_3',B_126,'#skF_5'),'#skF_3')
      | r1_tarski(k2_relset_1('#skF_3',B_126,'#skF_5'),B_126) ) ),
    inference(resolution,[status(thm)],[c_501,c_4])).

tff(c_767,plain,
    ( m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3')
    | r1_tarski(k2_relat_1('#skF_5'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_738,c_550])).

tff(c_778,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_710,c_767])).

tff(c_780,plain,(
    m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_708])).

tff(c_32,plain,(
    ! [A_22,B_23,C_24,D_25] :
      ( k3_funct_2(A_22,B_23,C_24,D_25) = k1_funct_1(C_24,D_25)
      | ~ m1_subset_1(D_25,A_22)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23)))
      | ~ v1_funct_2(C_24,A_22,B_23)
      | ~ v1_funct_1(C_24)
      | v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_782,plain,(
    ! [B_23,C_24] :
      ( k3_funct_2('#skF_3',B_23,C_24,'#skF_1'('#skF_3','#skF_2','#skF_5')) = k1_funct_1(C_24,'#skF_1'('#skF_3','#skF_2','#skF_5'))
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_23)))
      | ~ v1_funct_2(C_24,'#skF_3',B_23)
      | ~ v1_funct_1(C_24)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_780,c_32])).

tff(c_912,plain,(
    ! [B_160,C_161] :
      ( k3_funct_2('#skF_3',B_160,C_161,'#skF_1'('#skF_3','#skF_2','#skF_5')) = k1_funct_1(C_161,'#skF_1'('#skF_3','#skF_2','#skF_5'))
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_160)))
      | ~ v1_funct_2(C_161,'#skF_3',B_160)
      | ~ v1_funct_1(C_161) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_782])).

tff(c_929,plain,
    ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'('#skF_3','#skF_2','#skF_5')) = k1_funct_1('#skF_5','#skF_1'('#skF_3','#skF_2','#skF_5'))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_912])).

tff(c_940,plain,(
    k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'('#skF_3','#skF_2','#skF_5')) = k1_funct_1('#skF_5','#skF_1'('#skF_3','#skF_2','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_929])).

tff(c_950,plain,
    ( r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3','#skF_2','#skF_5')),'#skF_2')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_940,c_48])).

tff(c_961,plain,(
    r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3','#skF_2','#skF_5')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_780,c_950])).

tff(c_551,plain,(
    ! [C_127,B_128] :
      ( ~ r2_hidden(k1_funct_1(C_127,'#skF_1'(k1_relat_1(C_127),B_128,C_127)),B_128)
      | m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_127),B_128)))
      | ~ v1_funct_1(C_127)
      | ~ v1_relat_1(C_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_554,plain,(
    ! [B_128] :
      ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_128,'#skF_5')),B_128)
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),B_128)))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_551])).

tff(c_556,plain,(
    ! [B_128] :
      ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_128,'#skF_5')),B_128)
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_128))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_54,c_307,c_554])).

tff(c_977,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_961,c_556])).

tff(c_1032,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_977,c_6])).

tff(c_1026,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_977,c_18])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_179,plain,(
    ! [A_73,B_74,C_75] :
      ( r1_tarski(k2_relset_1(A_73,B_74,C_75),B_74)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(resolution,[status(thm)],[c_136,c_6])).

tff(c_189,plain,(
    ! [A_73,B_74,A_3] :
      ( r1_tarski(k2_relset_1(A_73,B_74,A_3),B_74)
      | ~ r1_tarski(A_3,k2_zfmisc_1(A_73,B_74)) ) ),
    inference(resolution,[status(thm)],[c_8,c_179])).

tff(c_1092,plain,
    ( r1_tarski(k2_relat_1('#skF_5'),'#skF_2')
    | ~ r1_tarski('#skF_5',k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1026,c_189])).

tff(c_1101,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1032,c_1092])).

tff(c_1103,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_1101])).

tff(c_1104,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_306])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1115,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1104,c_2])).

tff(c_1117,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1115])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:09:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.36/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.53  
% 3.36/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.53  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 3.36/1.53  
% 3.36/1.53  %Foreground sorts:
% 3.36/1.53  
% 3.36/1.53  
% 3.36/1.53  %Background operators:
% 3.36/1.53  
% 3.36/1.53  
% 3.36/1.53  %Foreground operators:
% 3.36/1.53  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.36/1.53  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.36/1.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.36/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.36/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.36/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.36/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.36/1.53  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.36/1.53  tff('#skF_5', type, '#skF_5': $i).
% 3.36/1.53  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.36/1.53  tff('#skF_2', type, '#skF_2': $i).
% 3.36/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.36/1.53  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.36/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.36/1.53  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.36/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.36/1.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.36/1.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.36/1.53  tff('#skF_4', type, '#skF_4': $i).
% 3.36/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.36/1.53  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.36/1.53  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 3.36/1.53  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.36/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.36/1.53  
% 3.52/1.55  tff(f_125, negated_conjecture, ~(![A, B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((![E]: (m1_subset_1(E, B) => r2_hidden(k3_funct_2(B, C, D, E), A))) => r1_tarski(k2_relset_1(B, C, D), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t191_funct_2)).
% 3.52/1.55  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.52/1.55  tff(f_43, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.52/1.55  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.52/1.55  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.52/1.55  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.52/1.55  tff(f_103, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(C) = A) & (![D]: (r2_hidden(D, A) => r2_hidden(k1_funct_1(C, D), B)))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_funct_2)).
% 3.52/1.55  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 3.52/1.55  tff(f_86, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 3.52/1.55  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.52/1.55  tff(f_34, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.52/1.55  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.52/1.55  tff(c_56, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.52/1.55  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.52/1.55  tff(c_121, plain, (![A_64, B_65, C_66]: (k2_relset_1(A_64, B_65, C_66)=k2_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.52/1.55  tff(c_130, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_121])).
% 3.52/1.55  tff(c_46, plain, (~r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.52/1.55  tff(c_131, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_46])).
% 3.52/1.55  tff(c_54, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.52/1.55  tff(c_52, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.52/1.55  tff(c_58, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.52/1.55  tff(c_12, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.52/1.55  tff(c_76, plain, (![B_51, A_52]: (v1_relat_1(B_51) | ~m1_subset_1(B_51, k1_zfmisc_1(A_52)) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.52/1.55  tff(c_82, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_50, c_76])).
% 3.52/1.55  tff(c_86, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_82])).
% 3.52/1.55  tff(c_101, plain, (![A_58, B_59, C_60]: (k1_relset_1(A_58, B_59, C_60)=k1_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.52/1.55  tff(c_110, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_101])).
% 3.52/1.55  tff(c_290, plain, (![B_97, A_98, C_99]: (k1_xboole_0=B_97 | k1_relset_1(A_98, B_97, C_99)=A_98 | ~v1_funct_2(C_99, A_98, B_97) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_98, B_97))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.52/1.55  tff(c_301, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_290])).
% 3.52/1.55  tff(c_306, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_110, c_301])).
% 3.52/1.55  tff(c_307, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_306])).
% 3.52/1.55  tff(c_313, plain, (![C_100, B_101]: (r2_hidden('#skF_1'(k1_relat_1(C_100), B_101, C_100), k1_relat_1(C_100)) | v1_funct_2(C_100, k1_relat_1(C_100), B_101) | ~v1_funct_1(C_100) | ~v1_relat_1(C_100))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.52/1.55  tff(c_319, plain, (![B_101]: (r2_hidden('#skF_1'('#skF_3', B_101, '#skF_5'), k1_relat_1('#skF_5')) | v1_funct_2('#skF_5', k1_relat_1('#skF_5'), B_101) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_307, c_313])).
% 3.52/1.55  tff(c_332, plain, (![B_102]: (r2_hidden('#skF_1'('#skF_3', B_102, '#skF_5'), '#skF_3') | v1_funct_2('#skF_5', '#skF_3', B_102))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_54, c_307, c_307, c_319])).
% 3.52/1.55  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.52/1.55  tff(c_336, plain, (![B_102]: (m1_subset_1('#skF_1'('#skF_3', B_102, '#skF_5'), '#skF_3') | v1_funct_2('#skF_5', '#skF_3', B_102))), inference(resolution, [status(thm)], [c_332, c_4])).
% 3.52/1.55  tff(c_614, plain, (![A_134, B_135, C_136, D_137]: (k3_funct_2(A_134, B_135, C_136, D_137)=k1_funct_1(C_136, D_137) | ~m1_subset_1(D_137, A_134) | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))) | ~v1_funct_2(C_136, A_134, B_135) | ~v1_funct_1(C_136) | v1_xboole_0(A_134))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.52/1.55  tff(c_626, plain, (![B_135, C_136, B_102]: (k3_funct_2('#skF_3', B_135, C_136, '#skF_1'('#skF_3', B_102, '#skF_5'))=k1_funct_1(C_136, '#skF_1'('#skF_3', B_102, '#skF_5')) | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_135))) | ~v1_funct_2(C_136, '#skF_3', B_135) | ~v1_funct_1(C_136) | v1_xboole_0('#skF_3') | v1_funct_2('#skF_5', '#skF_3', B_102))), inference(resolution, [status(thm)], [c_336, c_614])).
% 3.52/1.55  tff(c_657, plain, (![B_138, C_139, B_140]: (k3_funct_2('#skF_3', B_138, C_139, '#skF_1'('#skF_3', B_140, '#skF_5'))=k1_funct_1(C_139, '#skF_1'('#skF_3', B_140, '#skF_5')) | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_138))) | ~v1_funct_2(C_139, '#skF_3', B_138) | ~v1_funct_1(C_139) | v1_funct_2('#skF_5', '#skF_3', B_140))), inference(negUnitSimplification, [status(thm)], [c_58, c_626])).
% 3.52/1.55  tff(c_667, plain, (![B_140]: (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'('#skF_3', B_140, '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_140, '#skF_5')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | v1_funct_2('#skF_5', '#skF_3', B_140))), inference(resolution, [status(thm)], [c_50, c_657])).
% 3.52/1.55  tff(c_676, plain, (![B_141]: (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'('#skF_3', B_141, '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_141, '#skF_5')) | v1_funct_2('#skF_5', '#skF_3', B_141))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_667])).
% 3.52/1.55  tff(c_48, plain, (![E_41]: (r2_hidden(k3_funct_2('#skF_3', '#skF_4', '#skF_5', E_41), '#skF_2') | ~m1_subset_1(E_41, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.52/1.55  tff(c_695, plain, (![B_143]: (r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_143, '#skF_5')), '#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', B_143, '#skF_5'), '#skF_3') | v1_funct_2('#skF_5', '#skF_3', B_143))), inference(superposition, [status(thm), theory('equality')], [c_676, c_48])).
% 3.52/1.55  tff(c_390, plain, (![C_115, B_116]: (~r2_hidden(k1_funct_1(C_115, '#skF_1'(k1_relat_1(C_115), B_116, C_115)), B_116) | v1_funct_2(C_115, k1_relat_1(C_115), B_116) | ~v1_funct_1(C_115) | ~v1_relat_1(C_115))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.52/1.55  tff(c_393, plain, (![B_116]: (~r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_116, '#skF_5')), B_116) | v1_funct_2('#skF_5', k1_relat_1('#skF_5'), B_116) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_307, c_390])).
% 3.52/1.55  tff(c_395, plain, (![B_116]: (~r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_116, '#skF_5')), B_116) | v1_funct_2('#skF_5', '#skF_3', B_116))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_54, c_307, c_393])).
% 3.52/1.55  tff(c_708, plain, (~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3') | v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_695, c_395])).
% 3.52/1.55  tff(c_710, plain, (~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_708])).
% 3.52/1.55  tff(c_396, plain, (![C_117, B_118]: (r2_hidden('#skF_1'(k1_relat_1(C_117), B_118, C_117), k1_relat_1(C_117)) | m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_117), B_118))) | ~v1_funct_1(C_117) | ~v1_relat_1(C_117))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.52/1.55  tff(c_402, plain, (![B_118]: (r2_hidden('#skF_1'('#skF_3', B_118, '#skF_5'), k1_relat_1('#skF_5')) | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), B_118))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_307, c_396])).
% 3.52/1.55  tff(c_412, plain, (![B_120]: (r2_hidden('#skF_1'('#skF_3', B_120, '#skF_5'), '#skF_3') | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_120))))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_54, c_307, c_307, c_402])).
% 3.52/1.55  tff(c_18, plain, (![A_16, B_17, C_18]: (k2_relset_1(A_16, B_17, C_18)=k2_relat_1(C_18) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.52/1.55  tff(c_496, plain, (![B_125]: (k2_relset_1('#skF_3', B_125, '#skF_5')=k2_relat_1('#skF_5') | r2_hidden('#skF_1'('#skF_3', B_125, '#skF_5'), '#skF_3'))), inference(resolution, [status(thm)], [c_412, c_18])).
% 3.52/1.55  tff(c_500, plain, (![B_125]: (m1_subset_1('#skF_1'('#skF_3', B_125, '#skF_5'), '#skF_3') | k2_relset_1('#skF_3', B_125, '#skF_5')=k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_496, c_4])).
% 3.52/1.55  tff(c_738, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_500, c_710])).
% 3.52/1.55  tff(c_136, plain, (![A_67, B_68, C_69]: (m1_subset_1(k2_relset_1(A_67, B_68, C_69), k1_zfmisc_1(B_68)) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.52/1.55  tff(c_6, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.52/1.55  tff(c_157, plain, (![A_67, B_68, C_69]: (r1_tarski(k2_relset_1(A_67, B_68, C_69), B_68) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(resolution, [status(thm)], [c_136, c_6])).
% 3.52/1.55  tff(c_501, plain, (![B_126]: (r1_tarski(k2_relset_1('#skF_3', B_126, '#skF_5'), B_126) | r2_hidden('#skF_1'('#skF_3', B_126, '#skF_5'), '#skF_3'))), inference(resolution, [status(thm)], [c_412, c_157])).
% 3.52/1.55  tff(c_550, plain, (![B_126]: (m1_subset_1('#skF_1'('#skF_3', B_126, '#skF_5'), '#skF_3') | r1_tarski(k2_relset_1('#skF_3', B_126, '#skF_5'), B_126))), inference(resolution, [status(thm)], [c_501, c_4])).
% 3.52/1.55  tff(c_767, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3') | r1_tarski(k2_relat_1('#skF_5'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_738, c_550])).
% 3.52/1.55  tff(c_778, plain, $false, inference(negUnitSimplification, [status(thm)], [c_131, c_710, c_767])).
% 3.52/1.55  tff(c_780, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3')), inference(splitRight, [status(thm)], [c_708])).
% 3.52/1.55  tff(c_32, plain, (![A_22, B_23, C_24, D_25]: (k3_funct_2(A_22, B_23, C_24, D_25)=k1_funct_1(C_24, D_25) | ~m1_subset_1(D_25, A_22) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))) | ~v1_funct_2(C_24, A_22, B_23) | ~v1_funct_1(C_24) | v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.52/1.55  tff(c_782, plain, (![B_23, C_24]: (k3_funct_2('#skF_3', B_23, C_24, '#skF_1'('#skF_3', '#skF_2', '#skF_5'))=k1_funct_1(C_24, '#skF_1'('#skF_3', '#skF_2', '#skF_5')) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_23))) | ~v1_funct_2(C_24, '#skF_3', B_23) | ~v1_funct_1(C_24) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_780, c_32])).
% 3.52/1.55  tff(c_912, plain, (![B_160, C_161]: (k3_funct_2('#skF_3', B_160, C_161, '#skF_1'('#skF_3', '#skF_2', '#skF_5'))=k1_funct_1(C_161, '#skF_1'('#skF_3', '#skF_2', '#skF_5')) | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_160))) | ~v1_funct_2(C_161, '#skF_3', B_160) | ~v1_funct_1(C_161))), inference(negUnitSimplification, [status(thm)], [c_58, c_782])).
% 3.52/1.55  tff(c_929, plain, (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'('#skF_3', '#skF_2', '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'('#skF_3', '#skF_2', '#skF_5')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_912])).
% 3.52/1.55  tff(c_940, plain, (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'('#skF_3', '#skF_2', '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'('#skF_3', '#skF_2', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_929])).
% 3.52/1.55  tff(c_950, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', '#skF_2', '#skF_5')), '#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_940, c_48])).
% 3.52/1.55  tff(c_961, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', '#skF_2', '#skF_5')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_780, c_950])).
% 3.52/1.55  tff(c_551, plain, (![C_127, B_128]: (~r2_hidden(k1_funct_1(C_127, '#skF_1'(k1_relat_1(C_127), B_128, C_127)), B_128) | m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_127), B_128))) | ~v1_funct_1(C_127) | ~v1_relat_1(C_127))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.52/1.55  tff(c_554, plain, (![B_128]: (~r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_128, '#skF_5')), B_128) | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), B_128))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_307, c_551])).
% 3.52/1.55  tff(c_556, plain, (![B_128]: (~r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_128, '#skF_5')), B_128) | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_128))))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_54, c_307, c_554])).
% 3.52/1.55  tff(c_977, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(resolution, [status(thm)], [c_961, c_556])).
% 3.52/1.55  tff(c_1032, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_977, c_6])).
% 3.52/1.55  tff(c_1026, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_977, c_18])).
% 3.52/1.55  tff(c_8, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.52/1.55  tff(c_179, plain, (![A_73, B_74, C_75]: (r1_tarski(k2_relset_1(A_73, B_74, C_75), B_74) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(resolution, [status(thm)], [c_136, c_6])).
% 3.52/1.55  tff(c_189, plain, (![A_73, B_74, A_3]: (r1_tarski(k2_relset_1(A_73, B_74, A_3), B_74) | ~r1_tarski(A_3, k2_zfmisc_1(A_73, B_74)))), inference(resolution, [status(thm)], [c_8, c_179])).
% 3.52/1.55  tff(c_1092, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_2') | ~r1_tarski('#skF_5', k2_zfmisc_1('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1026, c_189])).
% 3.52/1.55  tff(c_1101, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1032, c_1092])).
% 3.52/1.55  tff(c_1103, plain, $false, inference(negUnitSimplification, [status(thm)], [c_131, c_1101])).
% 3.52/1.55  tff(c_1104, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_306])).
% 3.52/1.55  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.52/1.55  tff(c_1115, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1104, c_2])).
% 3.52/1.55  tff(c_1117, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_1115])).
% 3.52/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/1.55  
% 3.52/1.55  Inference rules
% 3.52/1.55  ----------------------
% 3.52/1.55  #Ref     : 0
% 3.52/1.55  #Sup     : 223
% 3.52/1.55  #Fact    : 0
% 3.52/1.55  #Define  : 0
% 3.52/1.55  #Split   : 4
% 3.52/1.55  #Chain   : 0
% 3.52/1.55  #Close   : 0
% 3.52/1.55  
% 3.52/1.55  Ordering : KBO
% 3.52/1.55  
% 3.52/1.55  Simplification rules
% 3.52/1.55  ----------------------
% 3.52/1.55  #Subsume      : 28
% 3.52/1.55  #Demod        : 152
% 3.52/1.55  #Tautology    : 45
% 3.52/1.55  #SimpNegUnit  : 9
% 3.52/1.55  #BackRed      : 12
% 3.52/1.55  
% 3.52/1.55  #Partial instantiations: 0
% 3.52/1.55  #Strategies tried      : 1
% 3.52/1.55  
% 3.52/1.55  Timing (in seconds)
% 3.52/1.55  ----------------------
% 3.52/1.55  Preprocessing        : 0.33
% 3.52/1.55  Parsing              : 0.18
% 3.52/1.55  CNF conversion       : 0.02
% 3.52/1.55  Main loop            : 0.43
% 3.52/1.55  Inferencing          : 0.16
% 3.52/1.55  Reduction            : 0.13
% 3.52/1.55  Demodulation         : 0.09
% 3.52/1.55  BG Simplification    : 0.03
% 3.52/1.55  Subsumption          : 0.08
% 3.52/1.55  Abstraction          : 0.03
% 3.52/1.55  MUC search           : 0.00
% 3.52/1.55  Cooper               : 0.00
% 3.52/1.56  Total                : 0.81
% 3.52/1.56  Index Insertion      : 0.00
% 3.52/1.56  Index Deletion       : 0.00
% 3.52/1.56  Index Matching       : 0.00
% 3.52/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
