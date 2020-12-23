%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:58 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.49s
% Verified   : 
% Statistics : Number of formulae       :  151 (1007 expanded)
%              Number of leaves         :   31 ( 325 expanded)
%              Depth                    :   16
%              Number of atoms          :  317 (3766 expanded)
%              Number of equality atoms :   83 (1338 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(f_104,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_2)).

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

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_56,plain,(
    ! [C_33,A_34,B_35] :
      ( v1_relat_1(C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_63,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_56])).

tff(c_273,plain,(
    ! [C_85,A_86,B_87] :
      ( v4_relat_1(C_85,A_86)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_280,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_273])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k1_relat_1(B_2),A_1)
      | ~ v4_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46,plain,
    ( r2_hidden('#skF_6',k1_relset_1('#skF_2','#skF_3','#skF_4'))
    | ~ r1_partfun1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_65,plain,(
    ~ r1_partfun1('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_42,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_64,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_56])).

tff(c_38,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_66,plain,(
    ! [C_36,A_37,B_38] :
      ( v4_relat_1(C_36,A_37)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_73,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_66])).

tff(c_32,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_55,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_36,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_93,plain,(
    ! [A_48,B_49,C_50] :
      ( k1_relset_1(A_48,B_49,C_50) = k1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_101,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_93])).

tff(c_116,plain,(
    ! [B_58,A_59,C_60] :
      ( k1_xboole_0 = B_58
      | k1_relset_1(A_59,B_58,C_60) = A_59
      | ~ v1_funct_2(C_60,A_59,B_58)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_59,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_122,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_116])).

tff(c_128,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_101,c_122])).

tff(c_129,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_128])).

tff(c_176,plain,(
    ! [A_66,B_67] :
      ( r2_hidden('#skF_1'(A_66,B_67),k1_relat_1(A_66))
      | r1_partfun1(A_66,B_67)
      | ~ r1_tarski(k1_relat_1(A_66),k1_relat_1(B_67))
      | ~ v1_funct_1(B_67)
      | ~ v1_relat_1(B_67)
      | ~ v1_funct_1(A_66)
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_100,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_93])).

tff(c_54,plain,(
    ! [E_32] :
      ( r1_partfun1('#skF_4','#skF_5')
      | k1_funct_1('#skF_5',E_32) = k1_funct_1('#skF_4',E_32)
      | ~ r2_hidden(E_32,k1_relset_1('#skF_2','#skF_3','#skF_4')) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_84,plain,(
    ! [E_32] :
      ( k1_funct_1('#skF_5',E_32) = k1_funct_1('#skF_4',E_32)
      | ~ r2_hidden(E_32,k1_relset_1('#skF_2','#skF_3','#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_54])).

tff(c_102,plain,(
    ! [E_32] :
      ( k1_funct_1('#skF_5',E_32) = k1_funct_1('#skF_4',E_32)
      | ~ r2_hidden(E_32,k1_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_84])).

tff(c_180,plain,(
    ! [B_67] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_67)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_67))
      | r1_partfun1('#skF_4',B_67)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_67))
      | ~ v1_funct_1(B_67)
      | ~ v1_relat_1(B_67)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_176,c_102])).

tff(c_190,plain,(
    ! [B_69] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_69)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_69))
      | r1_partfun1('#skF_4',B_69)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_69))
      | ~ v1_funct_1(B_69)
      | ~ v1_relat_1(B_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_42,c_180])).

tff(c_193,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_5'))
    | r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_190])).

tff(c_198,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_5'))
    | r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_38,c_193])).

tff(c_199,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_5'))
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_198])).

tff(c_211,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_199])).

tff(c_214,plain,
    ( ~ v4_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_211])).

tff(c_218,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_73,c_214])).

tff(c_220,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_199])).

tff(c_219,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_199])).

tff(c_245,plain,(
    ! [B_76,A_77] :
      ( k1_funct_1(B_76,'#skF_1'(A_77,B_76)) != k1_funct_1(A_77,'#skF_1'(A_77,B_76))
      | r1_partfun1(A_77,B_76)
      | ~ r1_tarski(k1_relat_1(A_77),k1_relat_1(B_76))
      | ~ v1_funct_1(B_76)
      | ~ v1_relat_1(B_76)
      | ~ v1_funct_1(A_77)
      | ~ v1_relat_1(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_247,plain,
    ( r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_245])).

tff(c_250,plain,(
    r1_partfun1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_42,c_64,c_38,c_220,c_129,c_247])).

tff(c_252,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_250])).

tff(c_254,plain,(
    r1_partfun1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_44,plain,
    ( k1_funct_1('#skF_5','#skF_6') != k1_funct_1('#skF_4','#skF_6')
    | ~ r1_partfun1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_256,plain,(
    k1_funct_1('#skF_5','#skF_6') != k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_44])).

tff(c_282,plain,(
    ! [A_88,B_89,C_90] :
      ( k1_relset_1(A_88,B_89,C_90) = k1_relat_1(C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_290,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_282])).

tff(c_305,plain,(
    ! [B_98,A_99,C_100] :
      ( k1_xboole_0 = B_98
      | k1_relset_1(A_99,B_98,C_100) = A_99
      | ~ v1_funct_2(C_100,A_99,B_98)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_99,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_311,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_305])).

tff(c_317,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_290,c_311])).

tff(c_318,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_317])).

tff(c_289,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_282])).

tff(c_253,plain,(
    r2_hidden('#skF_6',k1_relset_1('#skF_2','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_291,plain,(
    r2_hidden('#skF_6',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_253])).

tff(c_375,plain,(
    ! [B_111,C_112,A_113] :
      ( k1_funct_1(B_111,C_112) = k1_funct_1(A_113,C_112)
      | ~ r2_hidden(C_112,k1_relat_1(A_113))
      | ~ r1_partfun1(A_113,B_111)
      | ~ r1_tarski(k1_relat_1(A_113),k1_relat_1(B_111))
      | ~ v1_funct_1(B_111)
      | ~ v1_relat_1(B_111)
      | ~ v1_funct_1(A_113)
      | ~ v1_relat_1(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_381,plain,(
    ! [B_111] :
      ( k1_funct_1(B_111,'#skF_6') = k1_funct_1('#skF_4','#skF_6')
      | ~ r1_partfun1('#skF_4',B_111)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_111))
      | ~ v1_funct_1(B_111)
      | ~ v1_relat_1(B_111)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_291,c_375])).

tff(c_418,plain,(
    ! [B_116] :
      ( k1_funct_1(B_116,'#skF_6') = k1_funct_1('#skF_4','#skF_6')
      | ~ r1_partfun1('#skF_4',B_116)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_116))
      | ~ v1_funct_1(B_116)
      | ~ v1_relat_1(B_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_42,c_381])).

tff(c_421,plain,
    ( k1_funct_1('#skF_5','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_318,c_418])).

tff(c_426,plain,
    ( k1_funct_1('#skF_5','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_38,c_254,c_421])).

tff(c_427,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_256,c_426])).

tff(c_446,plain,
    ( ~ v4_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_427])).

tff(c_450,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_280,c_446])).

tff(c_452,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_451,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_457,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_451])).

tff(c_468,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_40])).

tff(c_469,plain,(
    ! [C_120,A_121,B_122] :
      ( v1_relat_1(C_120)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_477,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_468,c_469])).

tff(c_733,plain,(
    ! [C_174,A_175,B_176] :
      ( v4_relat_1(C_174,A_175)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(A_175,B_176))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_741,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_468,c_733])).

tff(c_478,plain,
    ( r2_hidden('#skF_6',k1_relset_1('#skF_3','#skF_3','#skF_4'))
    | ~ r1_partfun1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_46])).

tff(c_479,plain,(
    ~ r1_partfun1('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_478])).

tff(c_462,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_34])).

tff(c_476,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_462,c_469])).

tff(c_481,plain,(
    ! [C_125,A_126,B_127] :
      ( v4_relat_1(C_125,A_126)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_126,B_127))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_489,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_468,c_481])).

tff(c_463,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_36])).

tff(c_504,plain,(
    ! [A_133,B_134,C_135] :
      ( k1_relset_1(A_133,B_134,C_135) = k1_relat_1(C_135)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_511,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_462,c_504])).

tff(c_22,plain,(
    ! [B_13,C_14] :
      ( k1_relset_1(k1_xboole_0,B_13,C_14) = k1_xboole_0
      | ~ v1_funct_2(C_14,k1_xboole_0,B_13)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_543,plain,(
    ! [B_141,C_142] :
      ( k1_relset_1('#skF_3',B_141,C_142) = '#skF_3'
      | ~ v1_funct_2(C_142,'#skF_3',B_141)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_141))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_452,c_452,c_452,c_22])).

tff(c_546,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_462,c_543])).

tff(c_552,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_463,c_511,c_546])).

tff(c_630,plain,(
    ! [A_153,B_154] :
      ( r2_hidden('#skF_1'(A_153,B_154),k1_relat_1(A_153))
      | r1_partfun1(A_153,B_154)
      | ~ r1_tarski(k1_relat_1(A_153),k1_relat_1(B_154))
      | ~ v1_funct_1(B_154)
      | ~ v1_relat_1(B_154)
      | ~ v1_funct_1(A_153)
      | ~ v1_relat_1(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_512,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_468,c_504])).

tff(c_513,plain,(
    ! [E_32] :
      ( r1_partfun1('#skF_4','#skF_5')
      | k1_funct_1('#skF_5',E_32) = k1_funct_1('#skF_4',E_32)
      | ~ r2_hidden(E_32,k1_relset_1('#skF_3','#skF_3','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_54])).

tff(c_514,plain,(
    ! [E_32] :
      ( k1_funct_1('#skF_5',E_32) = k1_funct_1('#skF_4',E_32)
      | ~ r2_hidden(E_32,k1_relset_1('#skF_3','#skF_3','#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_479,c_513])).

tff(c_520,plain,(
    ! [E_32] :
      ( k1_funct_1('#skF_5',E_32) = k1_funct_1('#skF_4',E_32)
      | ~ r2_hidden(E_32,k1_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_512,c_514])).

tff(c_634,plain,(
    ! [B_154] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_154)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_154))
      | r1_partfun1('#skF_4',B_154)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_154))
      | ~ v1_funct_1(B_154)
      | ~ v1_relat_1(B_154)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_630,c_520])).

tff(c_644,plain,(
    ! [B_156] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_156)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_156))
      | r1_partfun1('#skF_4',B_156)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_156))
      | ~ v1_funct_1(B_156)
      | ~ v1_relat_1(B_156) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_477,c_42,c_634])).

tff(c_647,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_5'))
    | r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_552,c_644])).

tff(c_652,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_5'))
    | r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_476,c_38,c_647])).

tff(c_653,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_5'))
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_479,c_652])).

tff(c_657,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_653])).

tff(c_660,plain,
    ( ~ v4_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_657])).

tff(c_664,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_477,c_489,c_660])).

tff(c_666,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_653])).

tff(c_665,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_653])).

tff(c_705,plain,(
    ! [B_165,A_166] :
      ( k1_funct_1(B_165,'#skF_1'(A_166,B_165)) != k1_funct_1(A_166,'#skF_1'(A_166,B_165))
      | r1_partfun1(A_166,B_165)
      | ~ r1_tarski(k1_relat_1(A_166),k1_relat_1(B_165))
      | ~ v1_funct_1(B_165)
      | ~ v1_relat_1(B_165)
      | ~ v1_funct_1(A_166)
      | ~ v1_relat_1(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_707,plain,
    ( r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_665,c_705])).

tff(c_710,plain,(
    r1_partfun1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_477,c_42,c_476,c_38,c_666,c_552,c_707])).

tff(c_712,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_479,c_710])).

tff(c_714,plain,(
    r1_partfun1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_478])).

tff(c_725,plain,(
    k1_funct_1('#skF_5','#skF_6') != k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_714,c_44])).

tff(c_742,plain,(
    ! [A_177,B_178,C_179] :
      ( k1_relset_1(A_177,B_178,C_179) = k1_relat_1(C_179)
      | ~ m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1(A_177,B_178))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_749,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_462,c_742])).

tff(c_778,plain,(
    ! [B_183,C_184] :
      ( k1_relset_1('#skF_3',B_183,C_184) = '#skF_3'
      | ~ v1_funct_2(C_184,'#skF_3',B_183)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_183))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_452,c_452,c_452,c_22])).

tff(c_781,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_462,c_778])).

tff(c_787,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_463,c_749,c_781])).

tff(c_750,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_468,c_742])).

tff(c_713,plain,(
    r2_hidden('#skF_6',k1_relset_1('#skF_3','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_478])).

tff(c_755,plain,(
    r2_hidden('#skF_6',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_750,c_713])).

tff(c_872,plain,(
    ! [B_198,C_199,A_200] :
      ( k1_funct_1(B_198,C_199) = k1_funct_1(A_200,C_199)
      | ~ r2_hidden(C_199,k1_relat_1(A_200))
      | ~ r1_partfun1(A_200,B_198)
      | ~ r1_tarski(k1_relat_1(A_200),k1_relat_1(B_198))
      | ~ v1_funct_1(B_198)
      | ~ v1_relat_1(B_198)
      | ~ v1_funct_1(A_200)
      | ~ v1_relat_1(A_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_878,plain,(
    ! [B_198] :
      ( k1_funct_1(B_198,'#skF_6') = k1_funct_1('#skF_4','#skF_6')
      | ~ r1_partfun1('#skF_4',B_198)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_198))
      | ~ v1_funct_1(B_198)
      | ~ v1_relat_1(B_198)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_755,c_872])).

tff(c_885,plain,(
    ! [B_201] :
      ( k1_funct_1(B_201,'#skF_6') = k1_funct_1('#skF_4','#skF_6')
      | ~ r1_partfun1('#skF_4',B_201)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_201))
      | ~ v1_funct_1(B_201)
      | ~ v1_relat_1(B_201) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_477,c_42,c_878])).

tff(c_888,plain,
    ( k1_funct_1('#skF_5','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_787,c_885])).

tff(c_893,plain,
    ( k1_funct_1('#skF_5','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_476,c_38,c_714,c_888])).

tff(c_894,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_725,c_893])).

tff(c_900,plain,
    ( ~ v4_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_894])).

tff(c_904,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_477,c_741,c_900])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:48:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.32/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.56  
% 3.32/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.57  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.32/1.57  
% 3.32/1.57  %Foreground sorts:
% 3.32/1.57  
% 3.32/1.57  
% 3.32/1.57  %Background operators:
% 3.32/1.57  
% 3.32/1.57  
% 3.32/1.57  %Foreground operators:
% 3.32/1.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.32/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.32/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.32/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.32/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.32/1.57  tff('#skF_5', type, '#skF_5': $i).
% 3.32/1.57  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.32/1.57  tff('#skF_6', type, '#skF_6': $i).
% 3.32/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.32/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.32/1.57  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.32/1.57  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.32/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.32/1.57  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.32/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.32/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.32/1.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.32/1.57  tff('#skF_4', type, '#skF_4': $i).
% 3.32/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.32/1.57  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.32/1.57  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.32/1.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.32/1.57  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 3.32/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.32/1.57  
% 3.49/1.60  tff(f_104, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (r1_partfun1(C, D) <=> (![E]: (r2_hidden(E, k1_relset_1(A, B, C)) => (k1_funct_1(C, E) = k1_funct_1(D, E)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_2)).
% 3.49/1.60  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.49/1.60  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.49/1.60  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.49/1.60  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.49/1.60  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.49/1.60  tff(f_81, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) => (r1_partfun1(A, B) <=> (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_partfun1)).
% 3.49/1.60  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.49/1.60  tff(c_56, plain, (![C_33, A_34, B_35]: (v1_relat_1(C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.49/1.60  tff(c_63, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_56])).
% 3.49/1.60  tff(c_273, plain, (![C_85, A_86, B_87]: (v4_relat_1(C_85, A_86) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.49/1.60  tff(c_280, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_40, c_273])).
% 3.49/1.60  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k1_relat_1(B_2), A_1) | ~v4_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.49/1.60  tff(c_46, plain, (r2_hidden('#skF_6', k1_relset_1('#skF_2', '#skF_3', '#skF_4')) | ~r1_partfun1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.49/1.60  tff(c_65, plain, (~r1_partfun1('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_46])).
% 3.49/1.60  tff(c_42, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.49/1.60  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.49/1.60  tff(c_64, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_56])).
% 3.49/1.60  tff(c_38, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.49/1.60  tff(c_66, plain, (![C_36, A_37, B_38]: (v4_relat_1(C_36, A_37) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.49/1.60  tff(c_73, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_40, c_66])).
% 3.49/1.60  tff(c_32, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.49/1.60  tff(c_55, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_32])).
% 3.49/1.60  tff(c_36, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.49/1.60  tff(c_93, plain, (![A_48, B_49, C_50]: (k1_relset_1(A_48, B_49, C_50)=k1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.49/1.60  tff(c_101, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_93])).
% 3.49/1.60  tff(c_116, plain, (![B_58, A_59, C_60]: (k1_xboole_0=B_58 | k1_relset_1(A_59, B_58, C_60)=A_59 | ~v1_funct_2(C_60, A_59, B_58) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_59, B_58))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.49/1.60  tff(c_122, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_116])).
% 3.49/1.60  tff(c_128, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_101, c_122])).
% 3.49/1.60  tff(c_129, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_55, c_128])).
% 3.49/1.60  tff(c_176, plain, (![A_66, B_67]: (r2_hidden('#skF_1'(A_66, B_67), k1_relat_1(A_66)) | r1_partfun1(A_66, B_67) | ~r1_tarski(k1_relat_1(A_66), k1_relat_1(B_67)) | ~v1_funct_1(B_67) | ~v1_relat_1(B_67) | ~v1_funct_1(A_66) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.49/1.60  tff(c_100, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_93])).
% 3.49/1.60  tff(c_54, plain, (![E_32]: (r1_partfun1('#skF_4', '#skF_5') | k1_funct_1('#skF_5', E_32)=k1_funct_1('#skF_4', E_32) | ~r2_hidden(E_32, k1_relset_1('#skF_2', '#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.49/1.60  tff(c_84, plain, (![E_32]: (k1_funct_1('#skF_5', E_32)=k1_funct_1('#skF_4', E_32) | ~r2_hidden(E_32, k1_relset_1('#skF_2', '#skF_3', '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_65, c_54])).
% 3.49/1.60  tff(c_102, plain, (![E_32]: (k1_funct_1('#skF_5', E_32)=k1_funct_1('#skF_4', E_32) | ~r2_hidden(E_32, k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_84])).
% 3.49/1.60  tff(c_180, plain, (![B_67]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_67))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_67)) | r1_partfun1('#skF_4', B_67) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_67)) | ~v1_funct_1(B_67) | ~v1_relat_1(B_67) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_176, c_102])).
% 3.49/1.60  tff(c_190, plain, (![B_69]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_69))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_69)) | r1_partfun1('#skF_4', B_69) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_69)) | ~v1_funct_1(B_69) | ~v1_relat_1(B_69))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_42, c_180])).
% 3.49/1.60  tff(c_193, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_5'))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', '#skF_5')) | r1_partfun1('#skF_4', '#skF_5') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_129, c_190])).
% 3.49/1.60  tff(c_198, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_5'))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', '#skF_5')) | r1_partfun1('#skF_4', '#skF_5') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_38, c_193])).
% 3.49/1.60  tff(c_199, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_5'))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', '#skF_5')) | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_65, c_198])).
% 3.49/1.60  tff(c_211, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(splitLeft, [status(thm)], [c_199])).
% 3.49/1.60  tff(c_214, plain, (~v4_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_4, c_211])).
% 3.49/1.60  tff(c_218, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_63, c_73, c_214])).
% 3.49/1.60  tff(c_220, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(splitRight, [status(thm)], [c_199])).
% 3.49/1.60  tff(c_219, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_5'))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_199])).
% 3.49/1.60  tff(c_245, plain, (![B_76, A_77]: (k1_funct_1(B_76, '#skF_1'(A_77, B_76))!=k1_funct_1(A_77, '#skF_1'(A_77, B_76)) | r1_partfun1(A_77, B_76) | ~r1_tarski(k1_relat_1(A_77), k1_relat_1(B_76)) | ~v1_funct_1(B_76) | ~v1_relat_1(B_76) | ~v1_funct_1(A_77) | ~v1_relat_1(A_77))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.49/1.60  tff(c_247, plain, (r1_partfun1('#skF_4', '#skF_5') | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_219, c_245])).
% 3.49/1.60  tff(c_250, plain, (r1_partfun1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_42, c_64, c_38, c_220, c_129, c_247])).
% 3.49/1.60  tff(c_252, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_250])).
% 3.49/1.60  tff(c_254, plain, (r1_partfun1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_46])).
% 3.49/1.60  tff(c_44, plain, (k1_funct_1('#skF_5', '#skF_6')!=k1_funct_1('#skF_4', '#skF_6') | ~r1_partfun1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.49/1.60  tff(c_256, plain, (k1_funct_1('#skF_5', '#skF_6')!=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_254, c_44])).
% 3.49/1.60  tff(c_282, plain, (![A_88, B_89, C_90]: (k1_relset_1(A_88, B_89, C_90)=k1_relat_1(C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.49/1.60  tff(c_290, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_282])).
% 3.49/1.60  tff(c_305, plain, (![B_98, A_99, C_100]: (k1_xboole_0=B_98 | k1_relset_1(A_99, B_98, C_100)=A_99 | ~v1_funct_2(C_100, A_99, B_98) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_99, B_98))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.49/1.60  tff(c_311, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_305])).
% 3.49/1.60  tff(c_317, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_290, c_311])).
% 3.49/1.60  tff(c_318, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_55, c_317])).
% 3.49/1.60  tff(c_289, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_282])).
% 3.49/1.60  tff(c_253, plain, (r2_hidden('#skF_6', k1_relset_1('#skF_2', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_46])).
% 3.49/1.60  tff(c_291, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_289, c_253])).
% 3.49/1.60  tff(c_375, plain, (![B_111, C_112, A_113]: (k1_funct_1(B_111, C_112)=k1_funct_1(A_113, C_112) | ~r2_hidden(C_112, k1_relat_1(A_113)) | ~r1_partfun1(A_113, B_111) | ~r1_tarski(k1_relat_1(A_113), k1_relat_1(B_111)) | ~v1_funct_1(B_111) | ~v1_relat_1(B_111) | ~v1_funct_1(A_113) | ~v1_relat_1(A_113))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.49/1.60  tff(c_381, plain, (![B_111]: (k1_funct_1(B_111, '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~r1_partfun1('#skF_4', B_111) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_111)) | ~v1_funct_1(B_111) | ~v1_relat_1(B_111) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_291, c_375])).
% 3.49/1.60  tff(c_418, plain, (![B_116]: (k1_funct_1(B_116, '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~r1_partfun1('#skF_4', B_116) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_116)) | ~v1_funct_1(B_116) | ~v1_relat_1(B_116))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_42, c_381])).
% 3.49/1.60  tff(c_421, plain, (k1_funct_1('#skF_5', '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~r1_partfun1('#skF_4', '#skF_5') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_318, c_418])).
% 3.49/1.60  tff(c_426, plain, (k1_funct_1('#skF_5', '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_38, c_254, c_421])).
% 3.49/1.60  tff(c_427, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_256, c_426])).
% 3.49/1.60  tff(c_446, plain, (~v4_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_4, c_427])).
% 3.49/1.60  tff(c_450, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_63, c_280, c_446])).
% 3.49/1.60  tff(c_452, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_32])).
% 3.49/1.60  tff(c_451, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_32])).
% 3.49/1.60  tff(c_457, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_452, c_451])).
% 3.49/1.60  tff(c_468, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_457, c_40])).
% 3.49/1.60  tff(c_469, plain, (![C_120, A_121, B_122]: (v1_relat_1(C_120) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.49/1.60  tff(c_477, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_468, c_469])).
% 3.49/1.60  tff(c_733, plain, (![C_174, A_175, B_176]: (v4_relat_1(C_174, A_175) | ~m1_subset_1(C_174, k1_zfmisc_1(k2_zfmisc_1(A_175, B_176))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.49/1.60  tff(c_741, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_468, c_733])).
% 3.49/1.60  tff(c_478, plain, (r2_hidden('#skF_6', k1_relset_1('#skF_3', '#skF_3', '#skF_4')) | ~r1_partfun1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_457, c_46])).
% 3.49/1.60  tff(c_479, plain, (~r1_partfun1('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_478])).
% 3.49/1.60  tff(c_462, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_457, c_34])).
% 3.49/1.60  tff(c_476, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_462, c_469])).
% 3.49/1.60  tff(c_481, plain, (![C_125, A_126, B_127]: (v4_relat_1(C_125, A_126) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(A_126, B_127))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.49/1.60  tff(c_489, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_468, c_481])).
% 3.49/1.60  tff(c_463, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_457, c_36])).
% 3.49/1.60  tff(c_504, plain, (![A_133, B_134, C_135]: (k1_relset_1(A_133, B_134, C_135)=k1_relat_1(C_135) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.49/1.60  tff(c_511, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_462, c_504])).
% 3.49/1.60  tff(c_22, plain, (![B_13, C_14]: (k1_relset_1(k1_xboole_0, B_13, C_14)=k1_xboole_0 | ~v1_funct_2(C_14, k1_xboole_0, B_13) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_13))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.49/1.60  tff(c_543, plain, (![B_141, C_142]: (k1_relset_1('#skF_3', B_141, C_142)='#skF_3' | ~v1_funct_2(C_142, '#skF_3', B_141) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_141))))), inference(demodulation, [status(thm), theory('equality')], [c_452, c_452, c_452, c_452, c_22])).
% 3.49/1.60  tff(c_546, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_462, c_543])).
% 3.49/1.60  tff(c_552, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_463, c_511, c_546])).
% 3.49/1.60  tff(c_630, plain, (![A_153, B_154]: (r2_hidden('#skF_1'(A_153, B_154), k1_relat_1(A_153)) | r1_partfun1(A_153, B_154) | ~r1_tarski(k1_relat_1(A_153), k1_relat_1(B_154)) | ~v1_funct_1(B_154) | ~v1_relat_1(B_154) | ~v1_funct_1(A_153) | ~v1_relat_1(A_153))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.49/1.60  tff(c_512, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_468, c_504])).
% 3.49/1.60  tff(c_513, plain, (![E_32]: (r1_partfun1('#skF_4', '#skF_5') | k1_funct_1('#skF_5', E_32)=k1_funct_1('#skF_4', E_32) | ~r2_hidden(E_32, k1_relset_1('#skF_3', '#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_457, c_54])).
% 3.49/1.60  tff(c_514, plain, (![E_32]: (k1_funct_1('#skF_5', E_32)=k1_funct_1('#skF_4', E_32) | ~r2_hidden(E_32, k1_relset_1('#skF_3', '#skF_3', '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_479, c_513])).
% 3.49/1.60  tff(c_520, plain, (![E_32]: (k1_funct_1('#skF_5', E_32)=k1_funct_1('#skF_4', E_32) | ~r2_hidden(E_32, k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_512, c_514])).
% 3.49/1.60  tff(c_634, plain, (![B_154]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_154))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_154)) | r1_partfun1('#skF_4', B_154) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_154)) | ~v1_funct_1(B_154) | ~v1_relat_1(B_154) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_630, c_520])).
% 3.49/1.60  tff(c_644, plain, (![B_156]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_156))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_156)) | r1_partfun1('#skF_4', B_156) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_156)) | ~v1_funct_1(B_156) | ~v1_relat_1(B_156))), inference(demodulation, [status(thm), theory('equality')], [c_477, c_42, c_634])).
% 3.49/1.60  tff(c_647, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_5'))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', '#skF_5')) | r1_partfun1('#skF_4', '#skF_5') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_3') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_552, c_644])).
% 3.49/1.60  tff(c_652, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_5'))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', '#skF_5')) | r1_partfun1('#skF_4', '#skF_5') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_476, c_38, c_647])).
% 3.49/1.60  tff(c_653, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_5'))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', '#skF_5')) | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_479, c_652])).
% 3.49/1.60  tff(c_657, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_653])).
% 3.49/1.60  tff(c_660, plain, (~v4_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_4, c_657])).
% 3.49/1.60  tff(c_664, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_477, c_489, c_660])).
% 3.49/1.60  tff(c_666, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_653])).
% 3.49/1.60  tff(c_665, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_5'))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_653])).
% 3.49/1.60  tff(c_705, plain, (![B_165, A_166]: (k1_funct_1(B_165, '#skF_1'(A_166, B_165))!=k1_funct_1(A_166, '#skF_1'(A_166, B_165)) | r1_partfun1(A_166, B_165) | ~r1_tarski(k1_relat_1(A_166), k1_relat_1(B_165)) | ~v1_funct_1(B_165) | ~v1_relat_1(B_165) | ~v1_funct_1(A_166) | ~v1_relat_1(A_166))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.49/1.60  tff(c_707, plain, (r1_partfun1('#skF_4', '#skF_5') | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_665, c_705])).
% 3.49/1.60  tff(c_710, plain, (r1_partfun1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_477, c_42, c_476, c_38, c_666, c_552, c_707])).
% 3.49/1.60  tff(c_712, plain, $false, inference(negUnitSimplification, [status(thm)], [c_479, c_710])).
% 3.49/1.60  tff(c_714, plain, (r1_partfun1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_478])).
% 3.49/1.60  tff(c_725, plain, (k1_funct_1('#skF_5', '#skF_6')!=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_714, c_44])).
% 3.49/1.60  tff(c_742, plain, (![A_177, B_178, C_179]: (k1_relset_1(A_177, B_178, C_179)=k1_relat_1(C_179) | ~m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1(A_177, B_178))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.49/1.60  tff(c_749, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_462, c_742])).
% 3.49/1.60  tff(c_778, plain, (![B_183, C_184]: (k1_relset_1('#skF_3', B_183, C_184)='#skF_3' | ~v1_funct_2(C_184, '#skF_3', B_183) | ~m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_183))))), inference(demodulation, [status(thm), theory('equality')], [c_452, c_452, c_452, c_452, c_22])).
% 3.49/1.60  tff(c_781, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_462, c_778])).
% 3.49/1.60  tff(c_787, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_463, c_749, c_781])).
% 3.49/1.60  tff(c_750, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_468, c_742])).
% 3.49/1.60  tff(c_713, plain, (r2_hidden('#skF_6', k1_relset_1('#skF_3', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_478])).
% 3.49/1.60  tff(c_755, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_750, c_713])).
% 3.49/1.60  tff(c_872, plain, (![B_198, C_199, A_200]: (k1_funct_1(B_198, C_199)=k1_funct_1(A_200, C_199) | ~r2_hidden(C_199, k1_relat_1(A_200)) | ~r1_partfun1(A_200, B_198) | ~r1_tarski(k1_relat_1(A_200), k1_relat_1(B_198)) | ~v1_funct_1(B_198) | ~v1_relat_1(B_198) | ~v1_funct_1(A_200) | ~v1_relat_1(A_200))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.49/1.60  tff(c_878, plain, (![B_198]: (k1_funct_1(B_198, '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~r1_partfun1('#skF_4', B_198) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_198)) | ~v1_funct_1(B_198) | ~v1_relat_1(B_198) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_755, c_872])).
% 3.49/1.60  tff(c_885, plain, (![B_201]: (k1_funct_1(B_201, '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~r1_partfun1('#skF_4', B_201) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_201)) | ~v1_funct_1(B_201) | ~v1_relat_1(B_201))), inference(demodulation, [status(thm), theory('equality')], [c_477, c_42, c_878])).
% 3.49/1.60  tff(c_888, plain, (k1_funct_1('#skF_5', '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~r1_partfun1('#skF_4', '#skF_5') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_3') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_787, c_885])).
% 3.49/1.60  tff(c_893, plain, (k1_funct_1('#skF_5', '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_476, c_38, c_714, c_888])).
% 3.49/1.60  tff(c_894, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_725, c_893])).
% 3.49/1.60  tff(c_900, plain, (~v4_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_4, c_894])).
% 3.49/1.60  tff(c_904, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_477, c_741, c_900])).
% 3.49/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.49/1.60  
% 3.49/1.60  Inference rules
% 3.49/1.60  ----------------------
% 3.49/1.60  #Ref     : 3
% 3.49/1.60  #Sup     : 163
% 3.49/1.60  #Fact    : 0
% 3.49/1.60  #Define  : 0
% 3.49/1.60  #Split   : 9
% 3.49/1.60  #Chain   : 0
% 3.49/1.60  #Close   : 0
% 3.49/1.60  
% 3.49/1.60  Ordering : KBO
% 3.49/1.60  
% 3.49/1.60  Simplification rules
% 3.49/1.60  ----------------------
% 3.49/1.60  #Subsume      : 12
% 3.49/1.60  #Demod        : 231
% 3.49/1.60  #Tautology    : 75
% 3.49/1.60  #SimpNegUnit  : 24
% 3.49/1.60  #BackRed      : 11
% 3.49/1.60  
% 3.49/1.60  #Partial instantiations: 0
% 3.49/1.60  #Strategies tried      : 1
% 3.49/1.60  
% 3.49/1.60  Timing (in seconds)
% 3.49/1.60  ----------------------
% 3.49/1.60  Preprocessing        : 0.34
% 3.49/1.60  Parsing              : 0.17
% 3.49/1.60  CNF conversion       : 0.02
% 3.49/1.60  Main loop            : 0.47
% 3.49/1.60  Inferencing          : 0.18
% 3.49/1.60  Reduction            : 0.14
% 3.49/1.60  Demodulation         : 0.09
% 3.49/1.60  BG Simplification    : 0.03
% 3.49/1.60  Subsumption          : 0.07
% 3.49/1.60  Abstraction          : 0.02
% 3.49/1.60  MUC search           : 0.00
% 3.49/1.60  Cooper               : 0.00
% 3.49/1.60  Total                : 0.86
% 3.49/1.60  Index Insertion      : 0.00
% 3.49/1.60  Index Deletion       : 0.00
% 3.49/1.60  Index Matching       : 0.00
% 3.49/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
