%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1004+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:14 EST 2020

% Result     : Theorem 6.72s
% Output     : CNFRefutation 6.87s
% Verified   : 
% Statistics : Number of formulae       :  161 (2086 expanded)
%              Number of leaves         :   39 ( 627 expanded)
%              Depth                    :   18
%              Number of atoms          :  271 (7481 expanded)
%              Number of equality atoms :   80 (2971 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(f_121,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( ( v1_funct_1(E)
          & v1_funct_2(E,A,B)
          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [F] :
            ( ( v1_funct_1(F)
              & v1_funct_2(F,B,C)
              & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
           => ( ( C = k1_xboole_0
               => B = k1_xboole_0 )
             => r1_tarski(k8_relset_1(A,B,E,D),k8_relset_1(A,C,k1_partfun1(A,B,B,C,E,F),k7_relset_1(B,C,F,D))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_funct_2)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_97,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(k2_relat_1(B),k1_relat_1(C))
           => r1_tarski(k10_relat_1(B,A),k10_relat_1(k5_relat_1(B,C),k9_relat_1(C,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_funct_1)).

tff(f_72,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_58,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_88,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_68,plain,(
    ! [C_47,A_48,B_49] :
      ( v1_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_81,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_68])).

tff(c_42,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_80,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_68])).

tff(c_132,plain,(
    ! [A_61,B_62,C_63] :
      ( k2_relset_1(A_61,B_62,C_63) = k2_relat_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_145,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_132])).

tff(c_20,plain,(
    ! [A_13,B_14,C_15] :
      ( m1_subset_1(k2_relset_1(A_13,B_14,C_15),k1_zfmisc_1(B_14))
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_182,plain,
    ( m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_20])).

tff(c_186,plain,(
    m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_182])).

tff(c_34,plain,(
    ! [A_40,B_41] :
      ( r1_tarski(A_40,B_41)
      | ~ m1_subset_1(A_40,k1_zfmisc_1(B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_191,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_186,c_34])).

tff(c_40,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_53,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_44,plain,(
    v1_funct_2('#skF_6','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_82,plain,(
    ! [A_50,B_51,C_52] :
      ( k1_relset_1(A_50,B_51,C_52) = k1_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_94,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_82])).

tff(c_447,plain,(
    ! [B_122,A_123,C_124] :
      ( k1_xboole_0 = B_122
      | k1_relset_1(A_123,B_122,C_124) = A_123
      | ~ v1_funct_2(C_124,A_123,B_122)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_123,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_458,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_6') = '#skF_2'
    | ~ v1_funct_2('#skF_6','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_447])).

tff(c_466,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_6') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_94,c_458])).

tff(c_467,plain,(
    k1_relat_1('#skF_6') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_466])).

tff(c_32,plain,(
    ! [B_37,A_36,C_39] :
      ( r1_tarski(k10_relat_1(B_37,A_36),k10_relat_1(k5_relat_1(B_37,C_39),k9_relat_1(C_39,A_36)))
      | ~ r1_tarski(k2_relat_1(B_37),k1_relat_1(C_39))
      | ~ v1_relat_1(C_39)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_52,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_46,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_712,plain,(
    ! [A_170,F_167,D_171,E_169,B_168,C_172] :
      ( k1_partfun1(A_170,B_168,C_172,D_171,E_169,F_167) = k5_relat_1(E_169,F_167)
      | ~ m1_subset_1(F_167,k1_zfmisc_1(k2_zfmisc_1(C_172,D_171)))
      | ~ v1_funct_1(F_167)
      | ~ m1_subset_1(E_169,k1_zfmisc_1(k2_zfmisc_1(A_170,B_168)))
      | ~ v1_funct_1(E_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_720,plain,(
    ! [A_170,B_168,E_169] :
      ( k1_partfun1(A_170,B_168,'#skF_2','#skF_3',E_169,'#skF_6') = k5_relat_1(E_169,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_169,k1_zfmisc_1(k2_zfmisc_1(A_170,B_168)))
      | ~ v1_funct_1(E_169) ) ),
    inference(resolution,[status(thm)],[c_42,c_712])).

tff(c_777,plain,(
    ! [A_179,B_180,E_181] :
      ( k1_partfun1(A_179,B_180,'#skF_2','#skF_3',E_181,'#skF_6') = k5_relat_1(E_181,'#skF_6')
      | ~ m1_subset_1(E_181,k1_zfmisc_1(k2_zfmisc_1(A_179,B_180)))
      | ~ v1_funct_1(E_181) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_720])).

tff(c_791,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_777])).

tff(c_799,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_791])).

tff(c_834,plain,(
    ! [C_187,F_189,E_190,A_188,B_186,D_185] :
      ( m1_subset_1(k1_partfun1(A_188,B_186,C_187,D_185,E_190,F_189),k1_zfmisc_1(k2_zfmisc_1(A_188,D_185)))
      | ~ m1_subset_1(F_189,k1_zfmisc_1(k2_zfmisc_1(C_187,D_185)))
      | ~ v1_funct_1(F_189)
      | ~ m1_subset_1(E_190,k1_zfmisc_1(k2_zfmisc_1(A_188,B_186)))
      | ~ v1_funct_1(E_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_892,plain,
    ( m1_subset_1(k5_relat_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_799,c_834])).

tff(c_916,plain,(
    m1_subset_1(k5_relat_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_46,c_42,c_892])).

tff(c_30,plain,(
    ! [A_32,B_33,C_34,D_35] :
      ( k8_relset_1(A_32,B_33,C_34,D_35) = k10_relat_1(C_34,D_35)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_982,plain,(
    ! [D_35] : k8_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_5','#skF_6'),D_35) = k10_relat_1(k5_relat_1('#skF_5','#skF_6'),D_35) ),
    inference(resolution,[status(thm)],[c_916,c_30])).

tff(c_310,plain,(
    ! [A_90,B_91,C_92,D_93] :
      ( k8_relset_1(A_90,B_91,C_92,D_93) = k10_relat_1(C_92,D_93)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_324,plain,(
    ! [D_93] : k8_relset_1('#skF_1','#skF_2','#skF_5',D_93) = k10_relat_1('#skF_5',D_93) ),
    inference(resolution,[status(thm)],[c_48,c_310])).

tff(c_257,plain,(
    ! [A_78,B_79,C_80,D_81] :
      ( k7_relset_1(A_78,B_79,C_80,D_81) = k9_relat_1(C_80,D_81)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_270,plain,(
    ! [D_81] : k7_relset_1('#skF_2','#skF_3','#skF_6',D_81) = k9_relat_1('#skF_6',D_81) ),
    inference(resolution,[status(thm)],[c_42,c_257])).

tff(c_38,plain,(
    ~ r1_tarski(k8_relset_1('#skF_1','#skF_2','#skF_5','#skF_4'),k8_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_5','#skF_6'),k7_relset_1('#skF_2','#skF_3','#skF_6','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_272,plain,(
    ~ r1_tarski(k8_relset_1('#skF_1','#skF_2','#skF_5','#skF_4'),k8_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_5','#skF_6'),k9_relat_1('#skF_6','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_38])).

tff(c_334,plain,(
    ~ r1_tarski(k10_relat_1('#skF_5','#skF_4'),k8_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_5','#skF_6'),k9_relat_1('#skF_6','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_272])).

tff(c_806,plain,(
    ~ r1_tarski(k10_relat_1('#skF_5','#skF_4'),k8_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_5','#skF_6'),k9_relat_1('#skF_6','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_799,c_334])).

tff(c_2021,plain,(
    ~ r1_tarski(k10_relat_1('#skF_5','#skF_4'),k10_relat_1(k5_relat_1('#skF_5','#skF_6'),k9_relat_1('#skF_6','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_982,c_806])).

tff(c_2033,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),k1_relat_1('#skF_6'))
    | ~ v1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_2021])).

tff(c_2037,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_80,c_191,c_467,c_2033])).

tff(c_2039,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_2038,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_2044,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2039,c_2038])).

tff(c_2056,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2044,c_48])).

tff(c_2072,plain,(
    ! [C_255,A_256,B_257] :
      ( v1_relat_1(C_255)
      | ~ m1_subset_1(C_255,k1_zfmisc_1(k2_zfmisc_1(A_256,B_257))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_2085,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2056,c_2072])).

tff(c_2049,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2044,c_42])).

tff(c_2084,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2049,c_2072])).

tff(c_50,plain,(
    v1_funct_2('#skF_5','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_2051,plain,(
    v1_funct_2('#skF_5','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2044,c_50])).

tff(c_6,plain,(
    ! [C_6,A_4] :
      ( k1_xboole_0 = C_6
      | ~ v1_funct_2(C_6,A_4,k1_xboole_0)
      | k1_xboole_0 = A_4
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1(A_4,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2286,plain,(
    ! [C_290,A_291] :
      ( C_290 = '#skF_3'
      | ~ v1_funct_2(C_290,A_291,'#skF_3')
      | A_291 = '#skF_3'
      | ~ m1_subset_1(C_290,k1_zfmisc_1(k2_zfmisc_1(A_291,'#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2039,c_2039,c_2039,c_2039,c_6])).

tff(c_2300,plain,
    ( '#skF_5' = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_3')
    | '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_2056,c_2286])).

tff(c_2309,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2051,c_2300])).

tff(c_2310,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2309])).

tff(c_2097,plain,(
    ! [A_261,B_262,C_263] :
      ( k2_relset_1(A_261,B_262,C_263) = k2_relat_1(C_263)
      | ~ m1_subset_1(C_263,k1_zfmisc_1(k2_zfmisc_1(A_261,B_262))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2110,plain,(
    k2_relset_1('#skF_1','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2056,c_2097])).

tff(c_2170,plain,(
    ! [A_275,B_276,C_277] :
      ( m1_subset_1(k2_relset_1(A_275,B_276,C_277),k1_zfmisc_1(B_276))
      | ~ m1_subset_1(C_277,k1_zfmisc_1(k2_zfmisc_1(A_275,B_276))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2188,plain,
    ( m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2110,c_2170])).

tff(c_2197,plain,(
    m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2056,c_2188])).

tff(c_2203,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_2197,c_34])).

tff(c_2316,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2310,c_2203])).

tff(c_2050,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2044,c_44])).

tff(c_2329,plain,(
    v1_funct_2('#skF_6','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2310,c_2310,c_2050])).

tff(c_2137,plain,(
    ! [A_269,B_270,C_271] :
      ( k1_relset_1(A_269,B_270,C_271) = k1_relat_1(C_271)
      | ~ m1_subset_1(C_271,k1_zfmisc_1(k2_zfmisc_1(A_269,B_270))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2149,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2049,c_2137])).

tff(c_2319,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_6') = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2310,c_2310,c_2149])).

tff(c_2326,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2310,c_2310,c_2049])).

tff(c_2331,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2310,c_2039])).

tff(c_12,plain,(
    ! [B_5,C_6] :
      ( k1_relset_1(k1_xboole_0,B_5,C_6) = k1_xboole_0
      | ~ v1_funct_2(C_6,k1_xboole_0,B_5)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_5))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2480,plain,(
    ! [B_296,C_297] :
      ( k1_relset_1('#skF_1',B_296,C_297) = '#skF_1'
      | ~ v1_funct_2(C_297,'#skF_1',B_296)
      | ~ m1_subset_1(C_297,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_296))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2331,c_2331,c_2331,c_2331,c_12])).

tff(c_2483,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_6') = '#skF_1'
    | ~ v1_funct_2('#skF_6','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_2326,c_2480])).

tff(c_2497,plain,(
    k1_relat_1('#skF_6') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2329,c_2319,c_2483])).

tff(c_2327,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2310,c_2056])).

tff(c_3003,plain,(
    ! [B_374,C_378,E_375,D_377,F_373,A_376] :
      ( k1_partfun1(A_376,B_374,C_378,D_377,E_375,F_373) = k5_relat_1(E_375,F_373)
      | ~ m1_subset_1(F_373,k1_zfmisc_1(k2_zfmisc_1(C_378,D_377)))
      | ~ v1_funct_1(F_373)
      | ~ m1_subset_1(E_375,k1_zfmisc_1(k2_zfmisc_1(A_376,B_374)))
      | ~ v1_funct_1(E_375) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3005,plain,(
    ! [A_376,B_374,E_375] :
      ( k1_partfun1(A_376,B_374,'#skF_1','#skF_1',E_375,'#skF_6') = k5_relat_1(E_375,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_375,k1_zfmisc_1(k2_zfmisc_1(A_376,B_374)))
      | ~ v1_funct_1(E_375) ) ),
    inference(resolution,[status(thm)],[c_2326,c_3003])).

tff(c_3068,plain,(
    ! [A_385,B_386,E_387] :
      ( k1_partfun1(A_385,B_386,'#skF_1','#skF_1',E_387,'#skF_6') = k5_relat_1(E_387,'#skF_6')
      | ~ m1_subset_1(E_387,k1_zfmisc_1(k2_zfmisc_1(A_385,B_386)))
      | ~ v1_funct_1(E_387) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_3005])).

tff(c_3074,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2327,c_3068])).

tff(c_3088,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_3074])).

tff(c_3125,plain,(
    ! [A_394,D_391,F_395,C_393,B_392,E_396] :
      ( m1_subset_1(k1_partfun1(A_394,B_392,C_393,D_391,E_396,F_395),k1_zfmisc_1(k2_zfmisc_1(A_394,D_391)))
      | ~ m1_subset_1(F_395,k1_zfmisc_1(k2_zfmisc_1(C_393,D_391)))
      | ~ v1_funct_1(F_395)
      | ~ m1_subset_1(E_396,k1_zfmisc_1(k2_zfmisc_1(A_394,B_392)))
      | ~ v1_funct_1(E_396) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_3183,plain,
    ( m1_subset_1(k5_relat_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3088,c_3125])).

tff(c_3207,plain,(
    m1_subset_1(k5_relat_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2327,c_46,c_2326,c_3183])).

tff(c_3284,plain,(
    ! [D_35] : k8_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_5','#skF_6'),D_35) = k10_relat_1(k5_relat_1('#skF_5','#skF_6'),D_35) ),
    inference(resolution,[status(thm)],[c_3207,c_30])).

tff(c_2407,plain,(
    ! [D_35] : k8_relset_1('#skF_1','#skF_1','#skF_5',D_35) = k10_relat_1('#skF_5',D_35) ),
    inference(resolution,[status(thm)],[c_2327,c_30])).

tff(c_2251,plain,(
    ! [A_284,B_285,C_286,D_287] :
      ( k7_relset_1(A_284,B_285,C_286,D_287) = k9_relat_1(C_286,D_287)
      | ~ m1_subset_1(C_286,k1_zfmisc_1(k2_zfmisc_1(A_284,B_285))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2264,plain,(
    ! [D_287] : k7_relset_1('#skF_3','#skF_3','#skF_6',D_287) = k9_relat_1('#skF_6',D_287) ),
    inference(resolution,[status(thm)],[c_2049,c_2251])).

tff(c_2071,plain,(
    ~ r1_tarski(k8_relset_1('#skF_1','#skF_3','#skF_5','#skF_4'),k8_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_3','#skF_3','#skF_3','#skF_5','#skF_6'),k7_relset_1('#skF_3','#skF_3','#skF_6','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2044,c_2044,c_2044,c_2044,c_38])).

tff(c_2266,plain,(
    ~ r1_tarski(k8_relset_1('#skF_1','#skF_3','#skF_5','#skF_4'),k8_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_3','#skF_3','#skF_3','#skF_5','#skF_6'),k9_relat_1('#skF_6','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2264,c_2071])).

tff(c_2517,plain,(
    ~ r1_tarski(k8_relset_1('#skF_1','#skF_1','#skF_5','#skF_4'),k8_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_5','#skF_6'),k9_relat_1('#skF_6','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2310,c_2310,c_2310,c_2310,c_2310,c_2266])).

tff(c_2611,plain,(
    ~ r1_tarski(k10_relat_1('#skF_5','#skF_4'),k8_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_5','#skF_6'),k9_relat_1('#skF_6','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2407,c_2517])).

tff(c_3097,plain,(
    ~ r1_tarski(k10_relat_1('#skF_5','#skF_4'),k8_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_5','#skF_6'),k9_relat_1('#skF_6','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3088,c_2611])).

tff(c_4726,plain,(
    ~ r1_tarski(k10_relat_1('#skF_5','#skF_4'),k10_relat_1(k5_relat_1('#skF_5','#skF_6'),k9_relat_1('#skF_6','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3284,c_3097])).

tff(c_4738,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),k1_relat_1('#skF_6'))
    | ~ v1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_4726])).

tff(c_4742,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2085,c_2084,c_2316,c_2497,c_4738])).

tff(c_4743,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2309])).

tff(c_4750,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4743,c_2085])).

tff(c_4746,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4743,c_2203])).

tff(c_4969,plain,(
    ! [B_502,C_503] :
      ( k1_relset_1('#skF_3',B_502,C_503) = '#skF_3'
      | ~ v1_funct_2(C_503,'#skF_3',B_502)
      | ~ m1_subset_1(C_503,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_502))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2039,c_2039,c_2039,c_2039,c_12])).

tff(c_4980,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_2049,c_4969])).

tff(c_4985,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2050,c_2149,c_4980])).

tff(c_4754,plain,(
    v1_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4743,c_52])).

tff(c_4752,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4743,c_2056])).

tff(c_5302,plain,(
    ! [C_562,D_561,B_558,F_557,E_559,A_560] :
      ( k1_partfun1(A_560,B_558,C_562,D_561,E_559,F_557) = k5_relat_1(E_559,F_557)
      | ~ m1_subset_1(F_557,k1_zfmisc_1(k2_zfmisc_1(C_562,D_561)))
      | ~ v1_funct_1(F_557)
      | ~ m1_subset_1(E_559,k1_zfmisc_1(k2_zfmisc_1(A_560,B_558)))
      | ~ v1_funct_1(E_559) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_5312,plain,(
    ! [A_560,B_558,E_559] :
      ( k1_partfun1(A_560,B_558,'#skF_3','#skF_3',E_559,'#skF_6') = k5_relat_1(E_559,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_559,k1_zfmisc_1(k2_zfmisc_1(A_560,B_558)))
      | ~ v1_funct_1(E_559) ) ),
    inference(resolution,[status(thm)],[c_2049,c_5302])).

tff(c_5367,plain,(
    ! [A_569,B_570,E_571] :
      ( k1_partfun1(A_569,B_570,'#skF_3','#skF_3',E_571,'#skF_6') = k5_relat_1(E_571,'#skF_6')
      | ~ m1_subset_1(E_571,k1_zfmisc_1(k2_zfmisc_1(A_569,B_570)))
      | ~ v1_funct_1(E_571) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_5312])).

tff(c_5370,plain,
    ( k1_partfun1('#skF_1','#skF_3','#skF_3','#skF_3','#skF_3','#skF_6') = k5_relat_1('#skF_3','#skF_6')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4752,c_5367])).

tff(c_5384,plain,(
    k1_partfun1('#skF_1','#skF_3','#skF_3','#skF_3','#skF_3','#skF_6') = k5_relat_1('#skF_3','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4754,c_5370])).

tff(c_5424,plain,(
    ! [B_576,D_575,E_580,F_579,A_578,C_577] :
      ( m1_subset_1(k1_partfun1(A_578,B_576,C_577,D_575,E_580,F_579),k1_zfmisc_1(k2_zfmisc_1(A_578,D_575)))
      | ~ m1_subset_1(F_579,k1_zfmisc_1(k2_zfmisc_1(C_577,D_575)))
      | ~ v1_funct_1(F_579)
      | ~ m1_subset_1(E_580,k1_zfmisc_1(k2_zfmisc_1(A_578,B_576)))
      | ~ v1_funct_1(E_580) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_5482,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5384,c_5424])).

tff(c_5506,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4754,c_4752,c_46,c_2049,c_5482])).

tff(c_5573,plain,(
    ! [D_35] : k8_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_3','#skF_6'),D_35) = k10_relat_1(k5_relat_1('#skF_3','#skF_6'),D_35) ),
    inference(resolution,[status(thm)],[c_5506,c_30])).

tff(c_4836,plain,(
    ! [D_35] : k8_relset_1('#skF_1','#skF_3','#skF_3',D_35) = k10_relat_1('#skF_3',D_35) ),
    inference(resolution,[status(thm)],[c_4752,c_30])).

tff(c_4929,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3','#skF_4'),k8_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_3','#skF_3','#skF_3','#skF_3','#skF_6'),k9_relat_1('#skF_6','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4836,c_4743,c_4743,c_2266])).

tff(c_5396,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3','#skF_4'),k8_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_3','#skF_6'),k9_relat_1('#skF_6','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5384,c_4929])).

tff(c_6861,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3','#skF_4'),k10_relat_1(k5_relat_1('#skF_3','#skF_6'),k9_relat_1('#skF_6','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5573,c_5396])).

tff(c_6886,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),k1_relat_1('#skF_6'))
    | ~ v1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_6861])).

tff(c_6890,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4750,c_2084,c_4746,c_4985,c_6886])).

%------------------------------------------------------------------------------
