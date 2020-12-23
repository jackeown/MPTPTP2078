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
% DateTime   : Thu Dec  3 10:18:08 EST 2020

% Result     : Theorem 3.40s
% Output     : CNFRefutation 3.40s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 995 expanded)
%              Number of leaves         :   35 ( 363 expanded)
%              Depth                    :   24
%              Number of atoms          :  197 (3532 expanded)
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

tff(f_120,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t191_funct_2)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_68,axiom,(
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

tff(f_98,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_96,plain,(
    ! [A_56,B_57,C_58] :
      ( k2_relset_1(A_56,B_57,C_58) = k2_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_105,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_96])).

tff(c_44,plain,(
    ~ r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_106,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_44])).

tff(c_52,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_50,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_56,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_73,plain,(
    ! [C_47,A_48,B_49] :
      ( v1_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_82,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_73])).

tff(c_117,plain,(
    ! [A_62,B_63,C_64] :
      ( k1_relset_1(A_62,B_63,C_64) = k1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_126,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_117])).

tff(c_268,plain,(
    ! [B_97,A_98,C_99] :
      ( k1_xboole_0 = B_97
      | k1_relset_1(A_98,B_97,C_99) = A_98
      | ~ v1_funct_2(C_99,A_98,B_97)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_98,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_279,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_268])).

tff(c_284,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_126,c_279])).

tff(c_285,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_284])).

tff(c_336,plain,(
    ! [C_109,B_110] :
      ( r2_hidden('#skF_1'(k1_relat_1(C_109),B_110,C_109),k1_relat_1(C_109))
      | v1_funct_2(C_109,k1_relat_1(C_109),B_110)
      | ~ v1_funct_1(C_109)
      | ~ v1_relat_1(C_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_342,plain,(
    ! [B_110] :
      ( r2_hidden('#skF_1'('#skF_3',B_110,'#skF_5'),k1_relat_1('#skF_5'))
      | v1_funct_2('#skF_5',k1_relat_1('#skF_5'),B_110)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_336])).

tff(c_351,plain,(
    ! [B_111] :
      ( r2_hidden('#skF_1'('#skF_3',B_111,'#skF_5'),'#skF_3')
      | v1_funct_2('#skF_5','#skF_3',B_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_52,c_285,c_285,c_342])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_355,plain,(
    ! [B_111] :
      ( m1_subset_1('#skF_1'('#skF_3',B_111,'#skF_5'),'#skF_3')
      | v1_funct_2('#skF_5','#skF_3',B_111) ) ),
    inference(resolution,[status(thm)],[c_351,c_4])).

tff(c_587,plain,(
    ! [A_131,B_132,C_133,D_134] :
      ( k3_funct_2(A_131,B_132,C_133,D_134) = k1_funct_1(C_133,D_134)
      | ~ m1_subset_1(D_134,A_131)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132)))
      | ~ v1_funct_2(C_133,A_131,B_132)
      | ~ v1_funct_1(C_133)
      | v1_xboole_0(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_597,plain,(
    ! [B_132,C_133,B_111] :
      ( k3_funct_2('#skF_3',B_132,C_133,'#skF_1'('#skF_3',B_111,'#skF_5')) = k1_funct_1(C_133,'#skF_1'('#skF_3',B_111,'#skF_5'))
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_132)))
      | ~ v1_funct_2(C_133,'#skF_3',B_132)
      | ~ v1_funct_1(C_133)
      | v1_xboole_0('#skF_3')
      | v1_funct_2('#skF_5','#skF_3',B_111) ) ),
    inference(resolution,[status(thm)],[c_355,c_587])).

tff(c_626,plain,(
    ! [B_136,C_137,B_138] :
      ( k3_funct_2('#skF_3',B_136,C_137,'#skF_1'('#skF_3',B_138,'#skF_5')) = k1_funct_1(C_137,'#skF_1'('#skF_3',B_138,'#skF_5'))
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_136)))
      | ~ v1_funct_2(C_137,'#skF_3',B_136)
      | ~ v1_funct_1(C_137)
      | v1_funct_2('#skF_5','#skF_3',B_138) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_597])).

tff(c_636,plain,(
    ! [B_138] :
      ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'('#skF_3',B_138,'#skF_5')) = k1_funct_1('#skF_5','#skF_1'('#skF_3',B_138,'#skF_5'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5')
      | v1_funct_2('#skF_5','#skF_3',B_138) ) ),
    inference(resolution,[status(thm)],[c_48,c_626])).

tff(c_742,plain,(
    ! [B_149] :
      ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'('#skF_3',B_149,'#skF_5')) = k1_funct_1('#skF_5','#skF_1'('#skF_3',B_149,'#skF_5'))
      | v1_funct_2('#skF_5','#skF_3',B_149) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_636])).

tff(c_46,plain,(
    ! [E_39] :
      ( r2_hidden(k3_funct_2('#skF_3','#skF_4','#skF_5',E_39),'#skF_2')
      | ~ m1_subset_1(E_39,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_761,plain,(
    ! [B_151] :
      ( r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_151,'#skF_5')),'#skF_2')
      | ~ m1_subset_1('#skF_1'('#skF_3',B_151,'#skF_5'),'#skF_3')
      | v1_funct_2('#skF_5','#skF_3',B_151) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_742,c_46])).

tff(c_357,plain,(
    ! [C_113,B_114] :
      ( ~ r2_hidden(k1_funct_1(C_113,'#skF_1'(k1_relat_1(C_113),B_114,C_113)),B_114)
      | v1_funct_2(C_113,k1_relat_1(C_113),B_114)
      | ~ v1_funct_1(C_113)
      | ~ v1_relat_1(C_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_360,plain,(
    ! [B_114] :
      ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_114,'#skF_5')),B_114)
      | v1_funct_2('#skF_5',k1_relat_1('#skF_5'),B_114)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_357])).

tff(c_362,plain,(
    ! [B_114] :
      ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_114,'#skF_5')),B_114)
      | v1_funct_2('#skF_5','#skF_3',B_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_52,c_285,c_360])).

tff(c_774,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3')
    | v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_761,c_362])).

tff(c_776,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_774])).

tff(c_375,plain,(
    ! [C_118,B_119] :
      ( r2_hidden('#skF_1'(k1_relat_1(C_118),B_119,C_118),k1_relat_1(C_118))
      | m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_118),B_119)))
      | ~ v1_funct_1(C_118)
      | ~ v1_relat_1(C_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_381,plain,(
    ! [B_119] :
      ( r2_hidden('#skF_1'('#skF_3',B_119,'#skF_5'),k1_relat_1('#skF_5'))
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),B_119)))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_375])).

tff(c_390,plain,(
    ! [B_120] :
      ( r2_hidden('#skF_1'('#skF_3',B_120,'#skF_5'),'#skF_3')
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_120))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_52,c_285,c_285,c_381])).

tff(c_16,plain,(
    ! [A_14,B_15,C_16] :
      ( k2_relset_1(A_14,B_15,C_16) = k2_relat_1(C_16)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_531,plain,(
    ! [B_128] :
      ( k2_relset_1('#skF_3',B_128,'#skF_5') = k2_relat_1('#skF_5')
      | r2_hidden('#skF_1'('#skF_3',B_128,'#skF_5'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_390,c_16])).

tff(c_535,plain,(
    ! [B_128] :
      ( m1_subset_1('#skF_1'('#skF_3',B_128,'#skF_5'),'#skF_3')
      | k2_relset_1('#skF_3',B_128,'#skF_5') = k2_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_531,c_4])).

tff(c_803,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_535,c_776])).

tff(c_137,plain,(
    ! [A_68,B_69,C_70] :
      ( m1_subset_1(k2_relset_1(A_68,B_69,C_70),k1_zfmisc_1(B_69))
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_159,plain,(
    ! [A_68,B_69,C_70] :
      ( r1_tarski(k2_relset_1(A_68,B_69,C_70),B_69)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(resolution,[status(thm)],[c_137,c_6])).

tff(c_480,plain,(
    ! [B_127] :
      ( r1_tarski(k2_relset_1('#skF_3',B_127,'#skF_5'),B_127)
      | r2_hidden('#skF_1'('#skF_3',B_127,'#skF_5'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_390,c_159])).

tff(c_530,plain,(
    ! [B_127] :
      ( m1_subset_1('#skF_1'('#skF_3',B_127,'#skF_5'),'#skF_3')
      | r1_tarski(k2_relset_1('#skF_3',B_127,'#skF_5'),B_127) ) ),
    inference(resolution,[status(thm)],[c_480,c_4])).

tff(c_837,plain,
    ( m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3')
    | r1_tarski(k2_relat_1('#skF_5'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_803,c_530])).

tff(c_848,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_776,c_837])).

tff(c_850,plain,(
    m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_774])).

tff(c_30,plain,(
    ! [A_20,B_21,C_22,D_23] :
      ( k3_funct_2(A_20,B_21,C_22,D_23) = k1_funct_1(C_22,D_23)
      | ~ m1_subset_1(D_23,A_20)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21)))
      | ~ v1_funct_2(C_22,A_20,B_21)
      | ~ v1_funct_1(C_22)
      | v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_852,plain,(
    ! [B_21,C_22] :
      ( k3_funct_2('#skF_3',B_21,C_22,'#skF_1'('#skF_3','#skF_2','#skF_5')) = k1_funct_1(C_22,'#skF_1'('#skF_3','#skF_2','#skF_5'))
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_21)))
      | ~ v1_funct_2(C_22,'#skF_3',B_21)
      | ~ v1_funct_1(C_22)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_850,c_30])).

tff(c_967,plain,(
    ! [B_170,C_171] :
      ( k3_funct_2('#skF_3',B_170,C_171,'#skF_1'('#skF_3','#skF_2','#skF_5')) = k1_funct_1(C_171,'#skF_1'('#skF_3','#skF_2','#skF_5'))
      | ~ m1_subset_1(C_171,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_170)))
      | ~ v1_funct_2(C_171,'#skF_3',B_170)
      | ~ v1_funct_1(C_171) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_852])).

tff(c_984,plain,
    ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'('#skF_3','#skF_2','#skF_5')) = k1_funct_1('#skF_5','#skF_1'('#skF_3','#skF_2','#skF_5'))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_967])).

tff(c_995,plain,(
    k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'('#skF_3','#skF_2','#skF_5')) = k1_funct_1('#skF_5','#skF_1'('#skF_3','#skF_2','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_984])).

tff(c_1013,plain,
    ( r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3','#skF_2','#skF_5')),'#skF_2')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_995,c_46])).

tff(c_1029,plain,(
    r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3','#skF_2','#skF_5')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_850,c_1013])).

tff(c_435,plain,(
    ! [C_122,B_123] :
      ( ~ r2_hidden(k1_funct_1(C_122,'#skF_1'(k1_relat_1(C_122),B_123,C_122)),B_123)
      | m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_122),B_123)))
      | ~ v1_funct_1(C_122)
      | ~ v1_relat_1(C_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_438,plain,(
    ! [B_123] :
      ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_123,'#skF_5')),B_123)
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),B_123)))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_435])).

tff(c_440,plain,(
    ! [B_123] :
      ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_123,'#skF_5')),B_123)
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_123))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_52,c_285,c_438])).

tff(c_1047,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_1029,c_440])).

tff(c_1117,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1047,c_16])).

tff(c_1114,plain,(
    r1_tarski(k2_relset_1('#skF_3','#skF_2','#skF_5'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1047,c_159])).

tff(c_1176,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1117,c_1114])).

tff(c_1178,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_1176])).

tff(c_1179,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_284])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1190,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1179,c_2])).

tff(c_1192,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1190])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:03:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.40/1.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.40/1.58  
% 3.40/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.40/1.58  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 3.40/1.58  
% 3.40/1.58  %Foreground sorts:
% 3.40/1.58  
% 3.40/1.58  
% 3.40/1.58  %Background operators:
% 3.40/1.58  
% 3.40/1.58  
% 3.40/1.58  %Foreground operators:
% 3.40/1.58  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.40/1.58  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.40/1.58  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.40/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.40/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.40/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.40/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.40/1.58  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.40/1.58  tff('#skF_5', type, '#skF_5': $i).
% 3.40/1.58  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.40/1.58  tff('#skF_2', type, '#skF_2': $i).
% 3.40/1.58  tff('#skF_3', type, '#skF_3': $i).
% 3.40/1.58  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.40/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.40/1.58  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.40/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.40/1.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.40/1.58  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.40/1.58  tff('#skF_4', type, '#skF_4': $i).
% 3.40/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.40/1.58  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.40/1.58  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 3.40/1.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.40/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.40/1.58  
% 3.40/1.60  tff(f_120, negated_conjecture, ~(![A, B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((![E]: (m1_subset_1(E, B) => r2_hidden(k3_funct_2(B, C, D, E), A))) => r1_tarski(k2_relset_1(B, C, D), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t191_funct_2)).
% 3.40/1.60  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.40/1.60  tff(f_38, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.40/1.60  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.40/1.60  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.40/1.60  tff(f_98, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(C) = A) & (![D]: (r2_hidden(D, A) => r2_hidden(k1_funct_1(C, D), B)))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_funct_2)).
% 3.40/1.60  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 3.40/1.60  tff(f_81, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 3.40/1.60  tff(f_42, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.40/1.60  tff(f_34, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.40/1.60  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.40/1.60  tff(c_54, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.40/1.60  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.40/1.60  tff(c_96, plain, (![A_56, B_57, C_58]: (k2_relset_1(A_56, B_57, C_58)=k2_relat_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.40/1.60  tff(c_105, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_48, c_96])).
% 3.40/1.60  tff(c_44, plain, (~r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.40/1.60  tff(c_106, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_44])).
% 3.40/1.60  tff(c_52, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.40/1.60  tff(c_50, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.40/1.60  tff(c_56, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.40/1.60  tff(c_73, plain, (![C_47, A_48, B_49]: (v1_relat_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.40/1.60  tff(c_82, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_48, c_73])).
% 3.40/1.60  tff(c_117, plain, (![A_62, B_63, C_64]: (k1_relset_1(A_62, B_63, C_64)=k1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.40/1.60  tff(c_126, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_48, c_117])).
% 3.40/1.60  tff(c_268, plain, (![B_97, A_98, C_99]: (k1_xboole_0=B_97 | k1_relset_1(A_98, B_97, C_99)=A_98 | ~v1_funct_2(C_99, A_98, B_97) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_98, B_97))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.40/1.60  tff(c_279, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_48, c_268])).
% 3.40/1.60  tff(c_284, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_126, c_279])).
% 3.40/1.60  tff(c_285, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_284])).
% 3.40/1.60  tff(c_336, plain, (![C_109, B_110]: (r2_hidden('#skF_1'(k1_relat_1(C_109), B_110, C_109), k1_relat_1(C_109)) | v1_funct_2(C_109, k1_relat_1(C_109), B_110) | ~v1_funct_1(C_109) | ~v1_relat_1(C_109))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.40/1.60  tff(c_342, plain, (![B_110]: (r2_hidden('#skF_1'('#skF_3', B_110, '#skF_5'), k1_relat_1('#skF_5')) | v1_funct_2('#skF_5', k1_relat_1('#skF_5'), B_110) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_285, c_336])).
% 3.40/1.60  tff(c_351, plain, (![B_111]: (r2_hidden('#skF_1'('#skF_3', B_111, '#skF_5'), '#skF_3') | v1_funct_2('#skF_5', '#skF_3', B_111))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_52, c_285, c_285, c_342])).
% 3.40/1.60  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.40/1.60  tff(c_355, plain, (![B_111]: (m1_subset_1('#skF_1'('#skF_3', B_111, '#skF_5'), '#skF_3') | v1_funct_2('#skF_5', '#skF_3', B_111))), inference(resolution, [status(thm)], [c_351, c_4])).
% 3.40/1.60  tff(c_587, plain, (![A_131, B_132, C_133, D_134]: (k3_funct_2(A_131, B_132, C_133, D_134)=k1_funct_1(C_133, D_134) | ~m1_subset_1(D_134, A_131) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))) | ~v1_funct_2(C_133, A_131, B_132) | ~v1_funct_1(C_133) | v1_xboole_0(A_131))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.40/1.60  tff(c_597, plain, (![B_132, C_133, B_111]: (k3_funct_2('#skF_3', B_132, C_133, '#skF_1'('#skF_3', B_111, '#skF_5'))=k1_funct_1(C_133, '#skF_1'('#skF_3', B_111, '#skF_5')) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_132))) | ~v1_funct_2(C_133, '#skF_3', B_132) | ~v1_funct_1(C_133) | v1_xboole_0('#skF_3') | v1_funct_2('#skF_5', '#skF_3', B_111))), inference(resolution, [status(thm)], [c_355, c_587])).
% 3.40/1.60  tff(c_626, plain, (![B_136, C_137, B_138]: (k3_funct_2('#skF_3', B_136, C_137, '#skF_1'('#skF_3', B_138, '#skF_5'))=k1_funct_1(C_137, '#skF_1'('#skF_3', B_138, '#skF_5')) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_136))) | ~v1_funct_2(C_137, '#skF_3', B_136) | ~v1_funct_1(C_137) | v1_funct_2('#skF_5', '#skF_3', B_138))), inference(negUnitSimplification, [status(thm)], [c_56, c_597])).
% 3.40/1.60  tff(c_636, plain, (![B_138]: (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'('#skF_3', B_138, '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_138, '#skF_5')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | v1_funct_2('#skF_5', '#skF_3', B_138))), inference(resolution, [status(thm)], [c_48, c_626])).
% 3.40/1.60  tff(c_742, plain, (![B_149]: (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'('#skF_3', B_149, '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_149, '#skF_5')) | v1_funct_2('#skF_5', '#skF_3', B_149))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_636])).
% 3.40/1.60  tff(c_46, plain, (![E_39]: (r2_hidden(k3_funct_2('#skF_3', '#skF_4', '#skF_5', E_39), '#skF_2') | ~m1_subset_1(E_39, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.40/1.60  tff(c_761, plain, (![B_151]: (r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_151, '#skF_5')), '#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', B_151, '#skF_5'), '#skF_3') | v1_funct_2('#skF_5', '#skF_3', B_151))), inference(superposition, [status(thm), theory('equality')], [c_742, c_46])).
% 3.40/1.60  tff(c_357, plain, (![C_113, B_114]: (~r2_hidden(k1_funct_1(C_113, '#skF_1'(k1_relat_1(C_113), B_114, C_113)), B_114) | v1_funct_2(C_113, k1_relat_1(C_113), B_114) | ~v1_funct_1(C_113) | ~v1_relat_1(C_113))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.40/1.60  tff(c_360, plain, (![B_114]: (~r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_114, '#skF_5')), B_114) | v1_funct_2('#skF_5', k1_relat_1('#skF_5'), B_114) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_285, c_357])).
% 3.40/1.60  tff(c_362, plain, (![B_114]: (~r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_114, '#skF_5')), B_114) | v1_funct_2('#skF_5', '#skF_3', B_114))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_52, c_285, c_360])).
% 3.40/1.60  tff(c_774, plain, (~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3') | v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_761, c_362])).
% 3.40/1.60  tff(c_776, plain, (~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_774])).
% 3.40/1.60  tff(c_375, plain, (![C_118, B_119]: (r2_hidden('#skF_1'(k1_relat_1(C_118), B_119, C_118), k1_relat_1(C_118)) | m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_118), B_119))) | ~v1_funct_1(C_118) | ~v1_relat_1(C_118))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.40/1.60  tff(c_381, plain, (![B_119]: (r2_hidden('#skF_1'('#skF_3', B_119, '#skF_5'), k1_relat_1('#skF_5')) | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), B_119))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_285, c_375])).
% 3.40/1.60  tff(c_390, plain, (![B_120]: (r2_hidden('#skF_1'('#skF_3', B_120, '#skF_5'), '#skF_3') | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_120))))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_52, c_285, c_285, c_381])).
% 3.40/1.60  tff(c_16, plain, (![A_14, B_15, C_16]: (k2_relset_1(A_14, B_15, C_16)=k2_relat_1(C_16) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.40/1.60  tff(c_531, plain, (![B_128]: (k2_relset_1('#skF_3', B_128, '#skF_5')=k2_relat_1('#skF_5') | r2_hidden('#skF_1'('#skF_3', B_128, '#skF_5'), '#skF_3'))), inference(resolution, [status(thm)], [c_390, c_16])).
% 3.40/1.60  tff(c_535, plain, (![B_128]: (m1_subset_1('#skF_1'('#skF_3', B_128, '#skF_5'), '#skF_3') | k2_relset_1('#skF_3', B_128, '#skF_5')=k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_531, c_4])).
% 3.40/1.60  tff(c_803, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_535, c_776])).
% 3.40/1.60  tff(c_137, plain, (![A_68, B_69, C_70]: (m1_subset_1(k2_relset_1(A_68, B_69, C_70), k1_zfmisc_1(B_69)) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.40/1.60  tff(c_6, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.40/1.60  tff(c_159, plain, (![A_68, B_69, C_70]: (r1_tarski(k2_relset_1(A_68, B_69, C_70), B_69) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(resolution, [status(thm)], [c_137, c_6])).
% 3.40/1.60  tff(c_480, plain, (![B_127]: (r1_tarski(k2_relset_1('#skF_3', B_127, '#skF_5'), B_127) | r2_hidden('#skF_1'('#skF_3', B_127, '#skF_5'), '#skF_3'))), inference(resolution, [status(thm)], [c_390, c_159])).
% 3.40/1.60  tff(c_530, plain, (![B_127]: (m1_subset_1('#skF_1'('#skF_3', B_127, '#skF_5'), '#skF_3') | r1_tarski(k2_relset_1('#skF_3', B_127, '#skF_5'), B_127))), inference(resolution, [status(thm)], [c_480, c_4])).
% 3.40/1.60  tff(c_837, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3') | r1_tarski(k2_relat_1('#skF_5'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_803, c_530])).
% 3.40/1.60  tff(c_848, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106, c_776, c_837])).
% 3.40/1.60  tff(c_850, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3')), inference(splitRight, [status(thm)], [c_774])).
% 3.40/1.60  tff(c_30, plain, (![A_20, B_21, C_22, D_23]: (k3_funct_2(A_20, B_21, C_22, D_23)=k1_funct_1(C_22, D_23) | ~m1_subset_1(D_23, A_20) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))) | ~v1_funct_2(C_22, A_20, B_21) | ~v1_funct_1(C_22) | v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.40/1.60  tff(c_852, plain, (![B_21, C_22]: (k3_funct_2('#skF_3', B_21, C_22, '#skF_1'('#skF_3', '#skF_2', '#skF_5'))=k1_funct_1(C_22, '#skF_1'('#skF_3', '#skF_2', '#skF_5')) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_21))) | ~v1_funct_2(C_22, '#skF_3', B_21) | ~v1_funct_1(C_22) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_850, c_30])).
% 3.40/1.60  tff(c_967, plain, (![B_170, C_171]: (k3_funct_2('#skF_3', B_170, C_171, '#skF_1'('#skF_3', '#skF_2', '#skF_5'))=k1_funct_1(C_171, '#skF_1'('#skF_3', '#skF_2', '#skF_5')) | ~m1_subset_1(C_171, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_170))) | ~v1_funct_2(C_171, '#skF_3', B_170) | ~v1_funct_1(C_171))), inference(negUnitSimplification, [status(thm)], [c_56, c_852])).
% 3.40/1.60  tff(c_984, plain, (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'('#skF_3', '#skF_2', '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'('#skF_3', '#skF_2', '#skF_5')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_48, c_967])).
% 3.40/1.60  tff(c_995, plain, (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'('#skF_3', '#skF_2', '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'('#skF_3', '#skF_2', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_984])).
% 3.40/1.60  tff(c_1013, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', '#skF_2', '#skF_5')), '#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_995, c_46])).
% 3.40/1.60  tff(c_1029, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', '#skF_2', '#skF_5')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_850, c_1013])).
% 3.40/1.60  tff(c_435, plain, (![C_122, B_123]: (~r2_hidden(k1_funct_1(C_122, '#skF_1'(k1_relat_1(C_122), B_123, C_122)), B_123) | m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_122), B_123))) | ~v1_funct_1(C_122) | ~v1_relat_1(C_122))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.40/1.60  tff(c_438, plain, (![B_123]: (~r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_123, '#skF_5')), B_123) | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), B_123))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_285, c_435])).
% 3.40/1.60  tff(c_440, plain, (![B_123]: (~r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_123, '#skF_5')), B_123) | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_123))))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_52, c_285, c_438])).
% 3.40/1.60  tff(c_1047, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(resolution, [status(thm)], [c_1029, c_440])).
% 3.40/1.60  tff(c_1117, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1047, c_16])).
% 3.40/1.60  tff(c_1114, plain, (r1_tarski(k2_relset_1('#skF_3', '#skF_2', '#skF_5'), '#skF_2')), inference(resolution, [status(thm)], [c_1047, c_159])).
% 3.40/1.60  tff(c_1176, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1117, c_1114])).
% 3.40/1.60  tff(c_1178, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106, c_1176])).
% 3.40/1.60  tff(c_1179, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_284])).
% 3.40/1.60  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.40/1.60  tff(c_1190, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1179, c_2])).
% 3.40/1.60  tff(c_1192, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_1190])).
% 3.40/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.40/1.60  
% 3.40/1.60  Inference rules
% 3.40/1.60  ----------------------
% 3.40/1.60  #Ref     : 0
% 3.40/1.60  #Sup     : 237
% 3.40/1.60  #Fact    : 0
% 3.40/1.60  #Define  : 0
% 3.40/1.60  #Split   : 4
% 3.40/1.60  #Chain   : 0
% 3.40/1.60  #Close   : 0
% 3.40/1.60  
% 3.40/1.60  Ordering : KBO
% 3.40/1.60  
% 3.40/1.60  Simplification rules
% 3.40/1.60  ----------------------
% 3.40/1.60  #Subsume      : 26
% 3.40/1.60  #Demod        : 155
% 3.40/1.60  #Tautology    : 52
% 3.40/1.60  #SimpNegUnit  : 8
% 3.40/1.60  #BackRed      : 13
% 3.40/1.60  
% 3.40/1.60  #Partial instantiations: 0
% 3.40/1.60  #Strategies tried      : 1
% 3.40/1.60  
% 3.40/1.60  Timing (in seconds)
% 3.40/1.60  ----------------------
% 3.40/1.60  Preprocessing        : 0.33
% 3.40/1.60  Parsing              : 0.17
% 3.40/1.60  CNF conversion       : 0.02
% 3.40/1.60  Main loop            : 0.47
% 3.40/1.60  Inferencing          : 0.18
% 3.40/1.60  Reduction            : 0.14
% 3.40/1.61  Demodulation         : 0.10
% 3.40/1.61  BG Simplification    : 0.03
% 3.40/1.61  Subsumption          : 0.08
% 3.40/1.61  Abstraction          : 0.03
% 3.40/1.61  MUC search           : 0.00
% 3.40/1.61  Cooper               : 0.00
% 3.40/1.61  Total                : 0.84
% 3.40/1.61  Index Insertion      : 0.00
% 3.40/1.61  Index Deletion       : 0.00
% 3.40/1.61  Index Matching       : 0.00
% 3.40/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
