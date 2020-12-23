%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:12 EST 2020

% Result     : Theorem 2.39s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 321 expanded)
%              Number of leaves         :   26 ( 113 expanded)
%              Depth                    :   10
%              Number of atoms          :  174 (1046 expanded)
%              Number of equality atoms :   53 ( 324 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(k2_relset_1(A,B,D),C)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(D)
              & v1_funct_2(D,A,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_2)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_60,axiom,(
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

tff(f_72,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_167,plain,(
    ! [A_46,B_47,C_48] :
      ( k2_relset_1(A_46,B_47,C_48) = k2_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_171,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_167])).

tff(c_32,plain,(
    r1_tarski(k2_relset_1('#skF_1','#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_172,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_32])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_43,plain,(
    ! [B_19,A_20] :
      ( v1_relat_1(B_19)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(A_20))
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_46,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_43])).

tff(c_49,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_46])).

tff(c_38,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_30,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_36,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_177,plain,(
    ! [A_49,B_50,C_51] :
      ( k1_relset_1(A_49,B_50,C_51) = k1_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_181,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_177])).

tff(c_247,plain,(
    ! [B_70,A_71,C_72] :
      ( k1_xboole_0 = B_70
      | k1_relset_1(A_71,B_70,C_72) = A_71
      | ~ v1_funct_2(C_72,A_71,B_70)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_71,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_253,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_247])).

tff(c_257,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_181,c_253])).

tff(c_258,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_257])).

tff(c_22,plain,(
    ! [B_16,A_15] :
      ( m1_subset_1(B_16,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_16),A_15)))
      | ~ r1_tarski(k2_relat_1(B_16),A_15)
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_265,plain,(
    ! [A_15] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_15)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_15)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_22])).

tff(c_305,plain,(
    ! [A_75] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_75)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_75) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_38,c_265])).

tff(c_28,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_40,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_28])).

tff(c_50,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_51,plain,(
    ! [A_21,B_22,C_23] :
      ( k2_relset_1(A_21,B_22,C_23) = k2_relat_1(C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_55,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_51])).

tff(c_56,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_32])).

tff(c_61,plain,(
    ! [A_24,B_25,C_26] :
      ( k1_relset_1(A_24,B_25,C_26) = k1_relat_1(C_26)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_65,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_61])).

tff(c_116,plain,(
    ! [B_42,A_43,C_44] :
      ( k1_xboole_0 = B_42
      | k1_relset_1(A_43,B_42,C_44) = A_43
      | ~ v1_funct_2(C_44,A_43,B_42)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_43,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_122,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_116])).

tff(c_126,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_65,c_122])).

tff(c_127,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_126])).

tff(c_24,plain,(
    ! [B_16,A_15] :
      ( v1_funct_2(B_16,k1_relat_1(B_16),A_15)
      | ~ r1_tarski(k2_relat_1(B_16),A_15)
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_136,plain,(
    ! [A_15] :
      ( v1_funct_2('#skF_4','#skF_1',A_15)
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_15)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_24])).

tff(c_157,plain,(
    ! [A_45] :
      ( v1_funct_2('#skF_4','#skF_1',A_45)
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_45) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_38,c_136])).

tff(c_160,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_157])).

tff(c_164,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_160])).

tff(c_165,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_324,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_305,c_165])).

tff(c_337,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_324])).

tff(c_338,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_339,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_344,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_338,c_339])).

tff(c_351,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_344,c_34])).

tff(c_453,plain,(
    ! [A_94,B_95,C_96] :
      ( k2_relset_1(A_94,B_95,C_96) = k2_relat_1(C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_457,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_351,c_453])).

tff(c_350,plain,(
    r1_tarski(k2_relset_1('#skF_1','#skF_1','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_344,c_32])).

tff(c_458,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_350])).

tff(c_352,plain,(
    ! [B_76,A_77] :
      ( v1_relat_1(B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(A_77))
      | ~ v1_relat_1(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_355,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_351,c_352])).

tff(c_358,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_355])).

tff(c_345,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_344,c_36])).

tff(c_465,plain,(
    ! [A_98,B_99,C_100] :
      ( k1_relset_1(A_98,B_99,C_100) = k1_relat_1(C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_469,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_351,c_465])).

tff(c_18,plain,(
    ! [B_13,C_14] :
      ( k1_relset_1(k1_xboole_0,B_13,C_14) = k1_xboole_0
      | ~ v1_funct_2(C_14,k1_xboole_0,B_13)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_485,plain,(
    ! [B_105,C_106] :
      ( k1_relset_1('#skF_1',B_105,C_106) = '#skF_1'
      | ~ v1_funct_2(C_106,'#skF_1',B_105)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_105))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_338,c_338,c_338,c_338,c_18])).

tff(c_488,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_351,c_485])).

tff(c_491,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_469,c_488])).

tff(c_520,plain,(
    ! [B_110,A_111] :
      ( m1_subset_1(B_110,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_110),A_111)))
      | ~ r1_tarski(k2_relat_1(B_110),A_111)
      | ~ v1_funct_1(B_110)
      | ~ v1_relat_1(B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_540,plain,(
    ! [A_111] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_111)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_111)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_491,c_520])).

tff(c_563,plain,(
    ! [A_115] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_115)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_358,c_38,c_540])).

tff(c_359,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_371,plain,(
    ! [A_82,B_83,C_84] :
      ( k2_relset_1(A_82,B_83,C_84) = k2_relat_1(C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_375,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_351,c_371])).

tff(c_376,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_375,c_350])).

tff(c_362,plain,(
    ! [A_79,B_80,C_81] :
      ( k1_relset_1(A_79,B_80,C_81) = k1_relat_1(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_366,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_351,c_362])).

tff(c_392,plain,(
    ! [B_89,C_90] :
      ( k1_relset_1('#skF_1',B_89,C_90) = '#skF_1'
      | ~ v1_funct_2(C_90,'#skF_1',B_89)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_89))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_338,c_338,c_338,c_338,c_18])).

tff(c_395,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_351,c_392])).

tff(c_398,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_366,c_395])).

tff(c_431,plain,(
    ! [A_15] :
      ( v1_funct_2('#skF_4','#skF_1',A_15)
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_15)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_398,c_24])).

tff(c_443,plain,(
    ! [A_93] :
      ( v1_funct_2('#skF_4','#skF_1',A_93)
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_93) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_358,c_38,c_431])).

tff(c_446,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_376,c_443])).

tff(c_450,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_359,c_446])).

tff(c_451,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_585,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_563,c_451])).

tff(c_602,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_458,c_585])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:40:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.39/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.39/1.36  
% 2.39/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.39/1.37  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.39/1.37  
% 2.39/1.37  %Foreground sorts:
% 2.39/1.37  
% 2.39/1.37  
% 2.39/1.37  %Background operators:
% 2.39/1.37  
% 2.39/1.37  
% 2.39/1.37  %Foreground operators:
% 2.39/1.37  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.39/1.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.39/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.39/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.39/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.39/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.39/1.37  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.39/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.39/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.39/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.39/1.37  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.39/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.39/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.39/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.39/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.39/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.39/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.39/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.39/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.39/1.37  
% 2.71/1.39  tff(f_92, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(k2_relset_1(A, B, D), C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_2)).
% 2.71/1.39  tff(f_42, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.71/1.39  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.71/1.39  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.71/1.39  tff(f_38, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.71/1.39  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.71/1.39  tff(f_72, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 2.71/1.39  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.71/1.39  tff(c_167, plain, (![A_46, B_47, C_48]: (k2_relset_1(A_46, B_47, C_48)=k2_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.71/1.39  tff(c_171, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_167])).
% 2.71/1.39  tff(c_32, plain, (r1_tarski(k2_relset_1('#skF_1', '#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.71/1.39  tff(c_172, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_171, c_32])).
% 2.71/1.39  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.71/1.39  tff(c_43, plain, (![B_19, A_20]: (v1_relat_1(B_19) | ~m1_subset_1(B_19, k1_zfmisc_1(A_20)) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.71/1.39  tff(c_46, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_34, c_43])).
% 2.71/1.39  tff(c_49, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_46])).
% 2.71/1.39  tff(c_38, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.71/1.39  tff(c_30, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.71/1.39  tff(c_42, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_30])).
% 2.71/1.39  tff(c_36, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.71/1.39  tff(c_177, plain, (![A_49, B_50, C_51]: (k1_relset_1(A_49, B_50, C_51)=k1_relat_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.71/1.39  tff(c_181, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_177])).
% 2.71/1.39  tff(c_247, plain, (![B_70, A_71, C_72]: (k1_xboole_0=B_70 | k1_relset_1(A_71, B_70, C_72)=A_71 | ~v1_funct_2(C_72, A_71, B_70) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_71, B_70))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.71/1.39  tff(c_253, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_34, c_247])).
% 2.71/1.39  tff(c_257, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_181, c_253])).
% 2.71/1.39  tff(c_258, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_42, c_257])).
% 2.71/1.39  tff(c_22, plain, (![B_16, A_15]: (m1_subset_1(B_16, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_16), A_15))) | ~r1_tarski(k2_relat_1(B_16), A_15) | ~v1_funct_1(B_16) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.71/1.39  tff(c_265, plain, (![A_15]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_15))) | ~r1_tarski(k2_relat_1('#skF_4'), A_15) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_258, c_22])).
% 2.71/1.39  tff(c_305, plain, (![A_75]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_75))) | ~r1_tarski(k2_relat_1('#skF_4'), A_75))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_38, c_265])).
% 2.71/1.39  tff(c_28, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.71/1.39  tff(c_40, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_28])).
% 2.71/1.39  tff(c_50, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_40])).
% 2.71/1.39  tff(c_51, plain, (![A_21, B_22, C_23]: (k2_relset_1(A_21, B_22, C_23)=k2_relat_1(C_23) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.71/1.39  tff(c_55, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_51])).
% 2.71/1.39  tff(c_56, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_55, c_32])).
% 2.71/1.39  tff(c_61, plain, (![A_24, B_25, C_26]: (k1_relset_1(A_24, B_25, C_26)=k1_relat_1(C_26) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.71/1.39  tff(c_65, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_61])).
% 2.71/1.39  tff(c_116, plain, (![B_42, A_43, C_44]: (k1_xboole_0=B_42 | k1_relset_1(A_43, B_42, C_44)=A_43 | ~v1_funct_2(C_44, A_43, B_42) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_43, B_42))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.71/1.39  tff(c_122, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_34, c_116])).
% 2.71/1.39  tff(c_126, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_65, c_122])).
% 2.71/1.39  tff(c_127, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_42, c_126])).
% 2.71/1.39  tff(c_24, plain, (![B_16, A_15]: (v1_funct_2(B_16, k1_relat_1(B_16), A_15) | ~r1_tarski(k2_relat_1(B_16), A_15) | ~v1_funct_1(B_16) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.71/1.39  tff(c_136, plain, (![A_15]: (v1_funct_2('#skF_4', '#skF_1', A_15) | ~r1_tarski(k2_relat_1('#skF_4'), A_15) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_127, c_24])).
% 2.71/1.39  tff(c_157, plain, (![A_45]: (v1_funct_2('#skF_4', '#skF_1', A_45) | ~r1_tarski(k2_relat_1('#skF_4'), A_45))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_38, c_136])).
% 2.71/1.39  tff(c_160, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_56, c_157])).
% 2.71/1.39  tff(c_164, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_160])).
% 2.71/1.39  tff(c_165, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(splitRight, [status(thm)], [c_40])).
% 2.71/1.39  tff(c_324, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_305, c_165])).
% 2.71/1.39  tff(c_337, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_172, c_324])).
% 2.71/1.39  tff(c_338, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_30])).
% 2.71/1.39  tff(c_339, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_30])).
% 2.71/1.39  tff(c_344, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_338, c_339])).
% 2.71/1.39  tff(c_351, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_344, c_34])).
% 2.71/1.39  tff(c_453, plain, (![A_94, B_95, C_96]: (k2_relset_1(A_94, B_95, C_96)=k2_relat_1(C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.71/1.39  tff(c_457, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_351, c_453])).
% 2.71/1.39  tff(c_350, plain, (r1_tarski(k2_relset_1('#skF_1', '#skF_1', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_344, c_32])).
% 2.71/1.39  tff(c_458, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_457, c_350])).
% 2.71/1.39  tff(c_352, plain, (![B_76, A_77]: (v1_relat_1(B_76) | ~m1_subset_1(B_76, k1_zfmisc_1(A_77)) | ~v1_relat_1(A_77))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.71/1.39  tff(c_355, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_351, c_352])).
% 2.71/1.39  tff(c_358, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_355])).
% 2.71/1.39  tff(c_345, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_344, c_36])).
% 2.71/1.39  tff(c_465, plain, (![A_98, B_99, C_100]: (k1_relset_1(A_98, B_99, C_100)=k1_relat_1(C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.71/1.39  tff(c_469, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_351, c_465])).
% 2.71/1.39  tff(c_18, plain, (![B_13, C_14]: (k1_relset_1(k1_xboole_0, B_13, C_14)=k1_xboole_0 | ~v1_funct_2(C_14, k1_xboole_0, B_13) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_13))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.71/1.39  tff(c_485, plain, (![B_105, C_106]: (k1_relset_1('#skF_1', B_105, C_106)='#skF_1' | ~v1_funct_2(C_106, '#skF_1', B_105) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_105))))), inference(demodulation, [status(thm), theory('equality')], [c_338, c_338, c_338, c_338, c_18])).
% 2.71/1.39  tff(c_488, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_351, c_485])).
% 2.71/1.39  tff(c_491, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_345, c_469, c_488])).
% 2.71/1.39  tff(c_520, plain, (![B_110, A_111]: (m1_subset_1(B_110, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_110), A_111))) | ~r1_tarski(k2_relat_1(B_110), A_111) | ~v1_funct_1(B_110) | ~v1_relat_1(B_110))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.71/1.39  tff(c_540, plain, (![A_111]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_111))) | ~r1_tarski(k2_relat_1('#skF_4'), A_111) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_491, c_520])).
% 2.71/1.39  tff(c_563, plain, (![A_115]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_115))) | ~r1_tarski(k2_relat_1('#skF_4'), A_115))), inference(demodulation, [status(thm), theory('equality')], [c_358, c_38, c_540])).
% 2.71/1.39  tff(c_359, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_40])).
% 2.71/1.39  tff(c_371, plain, (![A_82, B_83, C_84]: (k2_relset_1(A_82, B_83, C_84)=k2_relat_1(C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.71/1.39  tff(c_375, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_351, c_371])).
% 2.71/1.39  tff(c_376, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_375, c_350])).
% 2.71/1.39  tff(c_362, plain, (![A_79, B_80, C_81]: (k1_relset_1(A_79, B_80, C_81)=k1_relat_1(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.71/1.39  tff(c_366, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_351, c_362])).
% 2.71/1.39  tff(c_392, plain, (![B_89, C_90]: (k1_relset_1('#skF_1', B_89, C_90)='#skF_1' | ~v1_funct_2(C_90, '#skF_1', B_89) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_89))))), inference(demodulation, [status(thm), theory('equality')], [c_338, c_338, c_338, c_338, c_18])).
% 2.71/1.39  tff(c_395, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_351, c_392])).
% 2.71/1.39  tff(c_398, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_345, c_366, c_395])).
% 2.71/1.39  tff(c_431, plain, (![A_15]: (v1_funct_2('#skF_4', '#skF_1', A_15) | ~r1_tarski(k2_relat_1('#skF_4'), A_15) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_398, c_24])).
% 2.71/1.39  tff(c_443, plain, (![A_93]: (v1_funct_2('#skF_4', '#skF_1', A_93) | ~r1_tarski(k2_relat_1('#skF_4'), A_93))), inference(demodulation, [status(thm), theory('equality')], [c_358, c_38, c_431])).
% 2.71/1.39  tff(c_446, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_376, c_443])).
% 2.71/1.39  tff(c_450, plain, $false, inference(negUnitSimplification, [status(thm)], [c_359, c_446])).
% 2.71/1.39  tff(c_451, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(splitRight, [status(thm)], [c_40])).
% 2.71/1.39  tff(c_585, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_563, c_451])).
% 2.71/1.39  tff(c_602, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_458, c_585])).
% 2.71/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.39  
% 2.71/1.39  Inference rules
% 2.71/1.39  ----------------------
% 2.71/1.39  #Ref     : 0
% 2.71/1.39  #Sup     : 126
% 2.71/1.39  #Fact    : 0
% 2.71/1.39  #Define  : 0
% 2.71/1.39  #Split   : 3
% 2.71/1.39  #Chain   : 0
% 2.71/1.39  #Close   : 0
% 2.71/1.39  
% 2.71/1.39  Ordering : KBO
% 2.71/1.39  
% 2.71/1.39  Simplification rules
% 2.71/1.39  ----------------------
% 2.71/1.39  #Subsume      : 11
% 2.71/1.39  #Demod        : 106
% 2.71/1.39  #Tautology    : 63
% 2.71/1.39  #SimpNegUnit  : 5
% 2.71/1.39  #BackRed      : 12
% 2.71/1.39  
% 2.71/1.39  #Partial instantiations: 0
% 2.71/1.39  #Strategies tried      : 1
% 2.71/1.39  
% 2.71/1.39  Timing (in seconds)
% 2.71/1.39  ----------------------
% 2.71/1.39  Preprocessing        : 0.30
% 2.71/1.39  Parsing              : 0.16
% 2.71/1.39  CNF conversion       : 0.02
% 2.71/1.39  Main loop            : 0.28
% 2.71/1.39  Inferencing          : 0.11
% 2.71/1.39  Reduction            : 0.09
% 2.71/1.39  Demodulation         : 0.06
% 2.71/1.39  BG Simplification    : 0.02
% 2.71/1.39  Subsumption          : 0.04
% 2.71/1.39  Abstraction          : 0.01
% 2.71/1.39  MUC search           : 0.00
% 2.71/1.39  Cooper               : 0.00
% 2.71/1.39  Total                : 0.63
% 2.71/1.39  Index Insertion      : 0.00
% 2.71/1.39  Index Deletion       : 0.00
% 2.71/1.39  Index Matching       : 0.00
% 2.71/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
