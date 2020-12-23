%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:43 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 193 expanded)
%              Number of leaves         :   36 (  88 expanded)
%              Depth                    :   10
%              Number of atoms          :  172 ( 795 expanded)
%              Number of equality atoms :   42 ( 172 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k8_funct_2,type,(
    k8_funct_2: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_121,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ v1_xboole_0(C)
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
           => ! [E] :
                ( ( v1_funct_1(E)
                  & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,A))) )
               => ! [F] :
                    ( m1_subset_1(F,B)
                   => ( r1_tarski(k2_relset_1(B,C,D),k1_relset_1(C,A,E))
                     => ( B = k1_xboole_0
                        | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k1_funct_1(E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_96,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_relat_1(E)
            & v1_funct_1(E) )
         => ( r2_hidden(C,A)
           => ( B = k1_xboole_0
              | k1_funct_1(k5_relat_1(D,E),C) = k1_funct_1(E,k1_funct_1(D,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_2)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_79,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( r1_tarski(k2_relset_1(A,B,D),k1_relset_1(B,C,E))
           => ( B = k1_xboole_0
              | k8_funct_2(A,B,C,D,E) = k1_partfun1(A,B,B,C,D,E) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_2)).

tff(f_37,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(c_28,plain,(
    m1_subset_1('#skF_7','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_30,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_74,plain,(
    ! [C_53,A_54,B_55] :
      ( v1_relat_1(C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_82,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_30,c_74])).

tff(c_32,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_38,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_36,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_105,plain,(
    ! [C_67,A_66,D_64,E_68,B_65] :
      ( k1_funct_1(k5_relat_1(D_64,E_68),C_67) = k1_funct_1(E_68,k1_funct_1(D_64,C_67))
      | k1_xboole_0 = B_65
      | ~ r2_hidden(C_67,A_66)
      | ~ v1_funct_1(E_68)
      | ~ v1_relat_1(E_68)
      | ~ m1_subset_1(D_64,k1_zfmisc_1(k2_zfmisc_1(A_66,B_65)))
      | ~ v1_funct_2(D_64,A_66,B_65)
      | ~ v1_funct_1(D_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_154,plain,(
    ! [D_75,E_76,A_77,B_78] :
      ( k1_funct_1(k5_relat_1(D_75,E_76),'#skF_1'(A_77)) = k1_funct_1(E_76,k1_funct_1(D_75,'#skF_1'(A_77)))
      | k1_xboole_0 = B_78
      | ~ v1_funct_1(E_76)
      | ~ v1_relat_1(E_76)
      | ~ m1_subset_1(D_75,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78)))
      | ~ v1_funct_2(D_75,A_77,B_78)
      | ~ v1_funct_1(D_75)
      | v1_xboole_0(A_77) ) ),
    inference(resolution,[status(thm)],[c_4,c_105])).

tff(c_156,plain,(
    ! [E_76] :
      ( k1_funct_1(k5_relat_1('#skF_5',E_76),'#skF_1'('#skF_3')) = k1_funct_1(E_76,k1_funct_1('#skF_5','#skF_1'('#skF_3')))
      | k1_xboole_0 = '#skF_4'
      | ~ v1_funct_1(E_76)
      | ~ v1_relat_1(E_76)
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5')
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_34,c_154])).

tff(c_161,plain,(
    ! [E_76] :
      ( k1_funct_1(k5_relat_1('#skF_5',E_76),'#skF_1'('#skF_3')) = k1_funct_1(E_76,k1_funct_1('#skF_5','#skF_1'('#skF_3')))
      | k1_xboole_0 = '#skF_4'
      | ~ v1_funct_1(E_76)
      | ~ v1_relat_1(E_76)
      | v1_xboole_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_156])).

tff(c_166,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_161])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_169,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_166,c_6])).

tff(c_173,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_169])).

tff(c_175,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_161])).

tff(c_40,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_94,plain,(
    ! [B_59,E_61,F_63,C_58,A_62,D_60] :
      ( k1_partfun1(A_62,B_59,C_58,D_60,E_61,F_63) = k5_relat_1(E_61,F_63)
      | ~ m1_subset_1(F_63,k1_zfmisc_1(k2_zfmisc_1(C_58,D_60)))
      | ~ v1_funct_1(F_63)
      | ~ m1_subset_1(E_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_59)))
      | ~ v1_funct_1(E_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_98,plain,(
    ! [A_62,B_59,E_61] :
      ( k1_partfun1(A_62,B_59,'#skF_4','#skF_2',E_61,'#skF_6') = k5_relat_1(E_61,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_59)))
      | ~ v1_funct_1(E_61) ) ),
    inference(resolution,[status(thm)],[c_30,c_94])).

tff(c_133,plain,(
    ! [A_72,B_73,E_74] :
      ( k1_partfun1(A_72,B_73,'#skF_4','#skF_2',E_74,'#skF_6') = k5_relat_1(E_74,'#skF_6')
      | ~ m1_subset_1(E_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73)))
      | ~ v1_funct_1(E_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_98])).

tff(c_136,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_2','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_133])).

tff(c_142,plain,(
    k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_2','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_136])).

tff(c_26,plain,(
    r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),k1_relset_1('#skF_4','#skF_2','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_176,plain,(
    ! [C_81,E_80,D_79,B_82,A_83] :
      ( k1_partfun1(A_83,B_82,B_82,C_81,D_79,E_80) = k8_funct_2(A_83,B_82,C_81,D_79,E_80)
      | k1_xboole_0 = B_82
      | ~ r1_tarski(k2_relset_1(A_83,B_82,D_79),k1_relset_1(B_82,C_81,E_80))
      | ~ m1_subset_1(E_80,k1_zfmisc_1(k2_zfmisc_1(B_82,C_81)))
      | ~ v1_funct_1(E_80)
      | ~ m1_subset_1(D_79,k1_zfmisc_1(k2_zfmisc_1(A_83,B_82)))
      | ~ v1_funct_2(D_79,A_83,B_82)
      | ~ v1_funct_1(D_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_179,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_2','#skF_5','#skF_6') = k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2')))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_176])).

tff(c_182,plain,
    ( k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_30,c_142,c_179])).

tff(c_183,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_182])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_45,plain,(
    ! [A_49] :
      ( v1_xboole_0(A_49)
      | r2_hidden('#skF_1'(A_49),A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( ~ r1_tarski(B_10,A_9)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_54,plain,(
    ! [A_50] :
      ( ~ r1_tarski(A_50,'#skF_1'(A_50))
      | v1_xboole_0(A_50) ) ),
    inference(resolution,[status(thm)],[c_45,c_12])).

tff(c_59,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_54])).

tff(c_187,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_59])).

tff(c_192,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_187])).

tff(c_194,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_182])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_211,plain,(
    ! [A_87,D_88,B_85,E_89,B_86] :
      ( k1_funct_1(k5_relat_1(D_88,E_89),A_87) = k1_funct_1(E_89,k1_funct_1(D_88,A_87))
      | k1_xboole_0 = B_85
      | ~ v1_funct_1(E_89)
      | ~ v1_relat_1(E_89)
      | ~ m1_subset_1(D_88,k1_zfmisc_1(k2_zfmisc_1(B_86,B_85)))
      | ~ v1_funct_2(D_88,B_86,B_85)
      | ~ v1_funct_1(D_88)
      | v1_xboole_0(B_86)
      | ~ m1_subset_1(A_87,B_86) ) ),
    inference(resolution,[status(thm)],[c_10,c_105])).

tff(c_213,plain,(
    ! [E_89,A_87] :
      ( k1_funct_1(k5_relat_1('#skF_5',E_89),A_87) = k1_funct_1(E_89,k1_funct_1('#skF_5',A_87))
      | k1_xboole_0 = '#skF_4'
      | ~ v1_funct_1(E_89)
      | ~ v1_relat_1(E_89)
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5')
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_87,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_34,c_211])).

tff(c_218,plain,(
    ! [E_89,A_87] :
      ( k1_funct_1(k5_relat_1('#skF_5',E_89),A_87) = k1_funct_1(E_89,k1_funct_1('#skF_5',A_87))
      | k1_xboole_0 = '#skF_4'
      | ~ v1_funct_1(E_89)
      | ~ v1_relat_1(E_89)
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_87,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_213])).

tff(c_224,plain,(
    ! [E_90,A_91] :
      ( k1_funct_1(k5_relat_1('#skF_5',E_90),A_91) = k1_funct_1(E_90,k1_funct_1('#skF_5',A_91))
      | ~ v1_funct_1(E_90)
      | ~ v1_relat_1(E_90)
      | ~ m1_subset_1(A_91,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_175,c_194,c_218])).

tff(c_193,plain,(
    k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_182])).

tff(c_22,plain,(
    k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_196,plain,(
    k1_funct_1(k5_relat_1('#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_22])).

tff(c_234,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ m1_subset_1('#skF_7','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_196])).

tff(c_246,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_82,c_32,c_234])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:10:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.62/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.34  
% 2.62/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.34  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 2.62/1.34  
% 2.62/1.34  %Foreground sorts:
% 2.62/1.34  
% 2.62/1.34  
% 2.62/1.34  %Background operators:
% 2.62/1.34  
% 2.62/1.34  
% 2.62/1.34  %Foreground operators:
% 2.62/1.34  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.62/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.62/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.62/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.62/1.34  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.62/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.62/1.34  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.62/1.34  tff('#skF_7', type, '#skF_7': $i).
% 2.62/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.62/1.34  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.62/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.62/1.34  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.62/1.34  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 2.62/1.34  tff('#skF_6', type, '#skF_6': $i).
% 2.62/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.62/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.62/1.34  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.62/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.62/1.34  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.62/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.62/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.62/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.62/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.62/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.62/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.62/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.62/1.34  
% 2.62/1.36  tff(f_121, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 2.62/1.36  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.62/1.36  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.62/1.36  tff(f_96, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_relat_1(E) & v1_funct_1(E)) => (r2_hidden(C, A) => ((B = k1_xboole_0) | (k1_funct_1(k5_relat_1(D, E), C) = k1_funct_1(E, k1_funct_1(D, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_funct_2)).
% 2.62/1.36  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.62/1.36  tff(f_79, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 2.62/1.36  tff(f_69, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (r1_tarski(k2_relset_1(A, B, D), k1_relset_1(B, C, E)) => ((B = k1_xboole_0) | (k8_funct_2(A, B, C, D, E) = k1_partfun1(A, B, B, C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_2)).
% 2.62/1.36  tff(f_37, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.62/1.36  tff(f_48, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.62/1.36  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.62/1.36  tff(c_28, plain, (m1_subset_1('#skF_7', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.62/1.36  tff(c_30, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.62/1.36  tff(c_74, plain, (![C_53, A_54, B_55]: (v1_relat_1(C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.62/1.36  tff(c_82, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_30, c_74])).
% 2.62/1.36  tff(c_32, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.62/1.36  tff(c_24, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.62/1.36  tff(c_38, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.62/1.36  tff(c_36, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.62/1.36  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.62/1.36  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.62/1.36  tff(c_105, plain, (![C_67, A_66, D_64, E_68, B_65]: (k1_funct_1(k5_relat_1(D_64, E_68), C_67)=k1_funct_1(E_68, k1_funct_1(D_64, C_67)) | k1_xboole_0=B_65 | ~r2_hidden(C_67, A_66) | ~v1_funct_1(E_68) | ~v1_relat_1(E_68) | ~m1_subset_1(D_64, k1_zfmisc_1(k2_zfmisc_1(A_66, B_65))) | ~v1_funct_2(D_64, A_66, B_65) | ~v1_funct_1(D_64))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.62/1.36  tff(c_154, plain, (![D_75, E_76, A_77, B_78]: (k1_funct_1(k5_relat_1(D_75, E_76), '#skF_1'(A_77))=k1_funct_1(E_76, k1_funct_1(D_75, '#skF_1'(A_77))) | k1_xboole_0=B_78 | ~v1_funct_1(E_76) | ~v1_relat_1(E_76) | ~m1_subset_1(D_75, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))) | ~v1_funct_2(D_75, A_77, B_78) | ~v1_funct_1(D_75) | v1_xboole_0(A_77))), inference(resolution, [status(thm)], [c_4, c_105])).
% 2.62/1.36  tff(c_156, plain, (![E_76]: (k1_funct_1(k5_relat_1('#skF_5', E_76), '#skF_1'('#skF_3'))=k1_funct_1(E_76, k1_funct_1('#skF_5', '#skF_1'('#skF_3'))) | k1_xboole_0='#skF_4' | ~v1_funct_1(E_76) | ~v1_relat_1(E_76) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_154])).
% 2.62/1.36  tff(c_161, plain, (![E_76]: (k1_funct_1(k5_relat_1('#skF_5', E_76), '#skF_1'('#skF_3'))=k1_funct_1(E_76, k1_funct_1('#skF_5', '#skF_1'('#skF_3'))) | k1_xboole_0='#skF_4' | ~v1_funct_1(E_76) | ~v1_relat_1(E_76) | v1_xboole_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_156])).
% 2.62/1.36  tff(c_166, plain, (v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_161])).
% 2.62/1.36  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.62/1.36  tff(c_169, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_166, c_6])).
% 2.62/1.36  tff(c_173, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_169])).
% 2.62/1.36  tff(c_175, plain, (~v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_161])).
% 2.62/1.36  tff(c_40, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.62/1.36  tff(c_94, plain, (![B_59, E_61, F_63, C_58, A_62, D_60]: (k1_partfun1(A_62, B_59, C_58, D_60, E_61, F_63)=k5_relat_1(E_61, F_63) | ~m1_subset_1(F_63, k1_zfmisc_1(k2_zfmisc_1(C_58, D_60))) | ~v1_funct_1(F_63) | ~m1_subset_1(E_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_59))) | ~v1_funct_1(E_61))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.62/1.36  tff(c_98, plain, (![A_62, B_59, E_61]: (k1_partfun1(A_62, B_59, '#skF_4', '#skF_2', E_61, '#skF_6')=k5_relat_1(E_61, '#skF_6') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_59))) | ~v1_funct_1(E_61))), inference(resolution, [status(thm)], [c_30, c_94])).
% 2.62/1.36  tff(c_133, plain, (![A_72, B_73, E_74]: (k1_partfun1(A_72, B_73, '#skF_4', '#skF_2', E_74, '#skF_6')=k5_relat_1(E_74, '#skF_6') | ~m1_subset_1(E_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))) | ~v1_funct_1(E_74))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_98])).
% 2.62/1.36  tff(c_136, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_133])).
% 2.62/1.36  tff(c_142, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_136])).
% 2.62/1.36  tff(c_26, plain, (r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), k1_relset_1('#skF_4', '#skF_2', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.62/1.36  tff(c_176, plain, (![C_81, E_80, D_79, B_82, A_83]: (k1_partfun1(A_83, B_82, B_82, C_81, D_79, E_80)=k8_funct_2(A_83, B_82, C_81, D_79, E_80) | k1_xboole_0=B_82 | ~r1_tarski(k2_relset_1(A_83, B_82, D_79), k1_relset_1(B_82, C_81, E_80)) | ~m1_subset_1(E_80, k1_zfmisc_1(k2_zfmisc_1(B_82, C_81))) | ~v1_funct_1(E_80) | ~m1_subset_1(D_79, k1_zfmisc_1(k2_zfmisc_1(A_83, B_82))) | ~v1_funct_2(D_79, A_83, B_82) | ~v1_funct_1(D_79))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.62/1.36  tff(c_179, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_26, c_176])).
% 2.62/1.36  tff(c_182, plain, (k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_30, c_142, c_179])).
% 2.62/1.36  tff(c_183, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_182])).
% 2.62/1.36  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.62/1.36  tff(c_45, plain, (![A_49]: (v1_xboole_0(A_49) | r2_hidden('#skF_1'(A_49), A_49))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.62/1.36  tff(c_12, plain, (![B_10, A_9]: (~r1_tarski(B_10, A_9) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.62/1.36  tff(c_54, plain, (![A_50]: (~r1_tarski(A_50, '#skF_1'(A_50)) | v1_xboole_0(A_50))), inference(resolution, [status(thm)], [c_45, c_12])).
% 2.62/1.36  tff(c_59, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_54])).
% 2.62/1.36  tff(c_187, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_183, c_59])).
% 2.62/1.36  tff(c_192, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_187])).
% 2.62/1.36  tff(c_194, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_182])).
% 2.62/1.36  tff(c_10, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.62/1.36  tff(c_211, plain, (![A_87, D_88, B_85, E_89, B_86]: (k1_funct_1(k5_relat_1(D_88, E_89), A_87)=k1_funct_1(E_89, k1_funct_1(D_88, A_87)) | k1_xboole_0=B_85 | ~v1_funct_1(E_89) | ~v1_relat_1(E_89) | ~m1_subset_1(D_88, k1_zfmisc_1(k2_zfmisc_1(B_86, B_85))) | ~v1_funct_2(D_88, B_86, B_85) | ~v1_funct_1(D_88) | v1_xboole_0(B_86) | ~m1_subset_1(A_87, B_86))), inference(resolution, [status(thm)], [c_10, c_105])).
% 2.62/1.36  tff(c_213, plain, (![E_89, A_87]: (k1_funct_1(k5_relat_1('#skF_5', E_89), A_87)=k1_funct_1(E_89, k1_funct_1('#skF_5', A_87)) | k1_xboole_0='#skF_4' | ~v1_funct_1(E_89) | ~v1_relat_1(E_89) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_3') | ~m1_subset_1(A_87, '#skF_3'))), inference(resolution, [status(thm)], [c_34, c_211])).
% 2.62/1.36  tff(c_218, plain, (![E_89, A_87]: (k1_funct_1(k5_relat_1('#skF_5', E_89), A_87)=k1_funct_1(E_89, k1_funct_1('#skF_5', A_87)) | k1_xboole_0='#skF_4' | ~v1_funct_1(E_89) | ~v1_relat_1(E_89) | v1_xboole_0('#skF_3') | ~m1_subset_1(A_87, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_213])).
% 2.62/1.36  tff(c_224, plain, (![E_90, A_91]: (k1_funct_1(k5_relat_1('#skF_5', E_90), A_91)=k1_funct_1(E_90, k1_funct_1('#skF_5', A_91)) | ~v1_funct_1(E_90) | ~v1_relat_1(E_90) | ~m1_subset_1(A_91, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_175, c_194, c_218])).
% 2.62/1.36  tff(c_193, plain, (k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_182])).
% 2.62/1.36  tff(c_22, plain, (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.62/1.36  tff(c_196, plain, (k1_funct_1(k5_relat_1('#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_193, c_22])).
% 2.62/1.36  tff(c_234, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~m1_subset_1('#skF_7', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_224, c_196])).
% 2.62/1.36  tff(c_246, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_82, c_32, c_234])).
% 2.62/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.36  
% 2.62/1.36  Inference rules
% 2.62/1.36  ----------------------
% 2.62/1.36  #Ref     : 0
% 2.62/1.36  #Sup     : 41
% 2.62/1.36  #Fact    : 0
% 2.62/1.36  #Define  : 0
% 2.62/1.36  #Split   : 4
% 2.62/1.36  #Chain   : 0
% 2.62/1.36  #Close   : 0
% 2.80/1.36  
% 2.80/1.36  Ordering : KBO
% 2.80/1.36  
% 2.80/1.36  Simplification rules
% 2.80/1.36  ----------------------
% 2.80/1.36  #Subsume      : 1
% 2.80/1.36  #Demod        : 30
% 2.80/1.36  #Tautology    : 18
% 2.80/1.36  #SimpNegUnit  : 6
% 2.80/1.36  #BackRed      : 8
% 2.80/1.36  
% 2.80/1.36  #Partial instantiations: 0
% 2.80/1.36  #Strategies tried      : 1
% 2.80/1.36  
% 2.80/1.36  Timing (in seconds)
% 2.80/1.36  ----------------------
% 2.80/1.37  Preprocessing        : 0.35
% 2.80/1.37  Parsing              : 0.19
% 2.80/1.37  CNF conversion       : 0.03
% 2.80/1.37  Main loop            : 0.24
% 2.80/1.37  Inferencing          : 0.09
% 2.80/1.37  Reduction            : 0.07
% 2.80/1.37  Demodulation         : 0.05
% 2.80/1.37  BG Simplification    : 0.02
% 2.80/1.37  Subsumption          : 0.04
% 2.80/1.37  Abstraction          : 0.01
% 2.80/1.37  MUC search           : 0.00
% 2.80/1.37  Cooper               : 0.00
% 2.80/1.37  Total                : 0.63
% 2.80/1.37  Index Insertion      : 0.00
% 2.80/1.37  Index Deletion       : 0.00
% 2.80/1.37  Index Matching       : 0.00
% 2.80/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
