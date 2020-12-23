%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:44 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 179 expanded)
%              Number of leaves         :   37 (  80 expanded)
%              Depth                    :   10
%              Number of atoms          :  180 ( 723 expanded)
%              Number of equality atoms :   44 ( 159 expanded)
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

tff(f_126,negated_conjecture,(
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
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_101,axiom,(
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

tff(f_37,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_57,axiom,(
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

tff(f_84,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_74,axiom,(
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

tff(c_30,plain,(
    m1_subset_1('#skF_7','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_14,plain,(
    ! [A_12,B_13] : v1_relat_1(k2_zfmisc_1(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_32,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_63,plain,(
    ! [B_55,A_56] :
      ( v1_relat_1(B_55)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_56))
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_69,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_63])).

tff(c_75,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_69])).

tff(c_34,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_40,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_38,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_154,plain,(
    ! [D_77,B_75,C_74,E_76,A_73] :
      ( k1_funct_1(k5_relat_1(D_77,E_76),C_74) = k1_funct_1(E_76,k1_funct_1(D_77,C_74))
      | k1_xboole_0 = B_75
      | ~ r2_hidden(C_74,A_73)
      | ~ v1_funct_1(E_76)
      | ~ v1_relat_1(E_76)
      | ~ m1_subset_1(D_77,k1_zfmisc_1(k2_zfmisc_1(A_73,B_75)))
      | ~ v1_funct_2(D_77,A_73,B_75)
      | ~ v1_funct_1(D_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_161,plain,(
    ! [D_78,E_79,A_80,B_81] :
      ( k1_funct_1(k5_relat_1(D_78,E_79),'#skF_1'(A_80)) = k1_funct_1(E_79,k1_funct_1(D_78,'#skF_1'(A_80)))
      | k1_xboole_0 = B_81
      | ~ v1_funct_1(E_79)
      | ~ v1_relat_1(E_79)
      | ~ m1_subset_1(D_78,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81)))
      | ~ v1_funct_2(D_78,A_80,B_81)
      | ~ v1_funct_1(D_78)
      | v1_xboole_0(A_80) ) ),
    inference(resolution,[status(thm)],[c_4,c_154])).

tff(c_163,plain,(
    ! [E_79] :
      ( k1_funct_1(k5_relat_1('#skF_5',E_79),'#skF_1'('#skF_3')) = k1_funct_1(E_79,k1_funct_1('#skF_5','#skF_1'('#skF_3')))
      | k1_xboole_0 = '#skF_4'
      | ~ v1_funct_1(E_79)
      | ~ v1_relat_1(E_79)
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5')
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_36,c_161])).

tff(c_168,plain,(
    ! [E_79] :
      ( k1_funct_1(k5_relat_1('#skF_5',E_79),'#skF_1'('#skF_3')) = k1_funct_1(E_79,k1_funct_1('#skF_5','#skF_1'('#skF_3')))
      | k1_xboole_0 = '#skF_4'
      | ~ v1_funct_1(E_79)
      | ~ v1_relat_1(E_79)
      | v1_xboole_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_163])).

tff(c_173,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_168])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_183,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_173,c_6])).

tff(c_187,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_183])).

tff(c_189,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_168])).

tff(c_42,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_188,plain,(
    ! [E_79] :
      ( k1_xboole_0 = '#skF_4'
      | k1_funct_1(k5_relat_1('#skF_5',E_79),'#skF_1'('#skF_3')) = k1_funct_1(E_79,k1_funct_1('#skF_5','#skF_1'('#skF_3')))
      | ~ v1_funct_1(E_79)
      | ~ v1_relat_1(E_79) ) ),
    inference(splitRight,[status(thm)],[c_168])).

tff(c_190,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_188])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_52,plain,(
    ! [B_52,A_53] :
      ( ~ r1_tarski(B_52,A_53)
      | ~ r2_hidden(A_53,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_57,plain,(
    ! [A_54] :
      ( ~ r1_tarski(A_54,'#skF_1'(A_54))
      | v1_xboole_0(A_54) ) ),
    inference(resolution,[status(thm)],[c_4,c_52])).

tff(c_62,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_57])).

tff(c_194,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_62])).

tff(c_199,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_194])).

tff(c_201,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_188])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_225,plain,(
    ! [A_95,B_96,D_94,B_93,E_97] :
      ( k1_funct_1(k5_relat_1(D_94,E_97),A_95) = k1_funct_1(E_97,k1_funct_1(D_94,A_95))
      | k1_xboole_0 = B_96
      | ~ v1_funct_1(E_97)
      | ~ v1_relat_1(E_97)
      | ~ m1_subset_1(D_94,k1_zfmisc_1(k2_zfmisc_1(B_93,B_96)))
      | ~ v1_funct_2(D_94,B_93,B_96)
      | ~ v1_funct_1(D_94)
      | v1_xboole_0(B_93)
      | ~ m1_subset_1(A_95,B_93) ) ),
    inference(resolution,[status(thm)],[c_10,c_154])).

tff(c_227,plain,(
    ! [E_97,A_95] :
      ( k1_funct_1(k5_relat_1('#skF_5',E_97),A_95) = k1_funct_1(E_97,k1_funct_1('#skF_5',A_95))
      | k1_xboole_0 = '#skF_4'
      | ~ v1_funct_1(E_97)
      | ~ v1_relat_1(E_97)
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5')
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_95,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_36,c_225])).

tff(c_232,plain,(
    ! [E_97,A_95] :
      ( k1_funct_1(k5_relat_1('#skF_5',E_97),A_95) = k1_funct_1(E_97,k1_funct_1('#skF_5',A_95))
      | k1_xboole_0 = '#skF_4'
      | ~ v1_funct_1(E_97)
      | ~ v1_relat_1(E_97)
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_95,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_227])).

tff(c_238,plain,(
    ! [E_98,A_99] :
      ( k1_funct_1(k5_relat_1('#skF_5',E_98),A_99) = k1_funct_1(E_98,k1_funct_1('#skF_5',A_99))
      | ~ v1_funct_1(E_98)
      | ~ v1_relat_1(E_98)
      | ~ m1_subset_1(A_99,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_189,c_201,c_232])).

tff(c_101,plain,(
    ! [B_66,A_61,F_64,C_62,E_63,D_65] :
      ( k1_partfun1(A_61,B_66,C_62,D_65,E_63,F_64) = k5_relat_1(E_63,F_64)
      | ~ m1_subset_1(F_64,k1_zfmisc_1(k2_zfmisc_1(C_62,D_65)))
      | ~ v1_funct_1(F_64)
      | ~ m1_subset_1(E_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_66)))
      | ~ v1_funct_1(E_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_105,plain,(
    ! [A_61,B_66,E_63] :
      ( k1_partfun1(A_61,B_66,'#skF_4','#skF_2',E_63,'#skF_6') = k5_relat_1(E_63,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_66)))
      | ~ v1_funct_1(E_63) ) ),
    inference(resolution,[status(thm)],[c_32,c_101])).

tff(c_133,plain,(
    ! [A_70,B_71,E_72] :
      ( k1_partfun1(A_70,B_71,'#skF_4','#skF_2',E_72,'#skF_6') = k5_relat_1(E_72,'#skF_6')
      | ~ m1_subset_1(E_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71)))
      | ~ v1_funct_1(E_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_105])).

tff(c_136,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_2','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_133])).

tff(c_142,plain,(
    k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_2','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_136])).

tff(c_28,plain,(
    r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),k1_relset_1('#skF_4','#skF_2','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_212,plain,(
    ! [C_92,B_88,D_91,E_89,A_90] :
      ( k1_partfun1(A_90,B_88,B_88,C_92,D_91,E_89) = k8_funct_2(A_90,B_88,C_92,D_91,E_89)
      | k1_xboole_0 = B_88
      | ~ r1_tarski(k2_relset_1(A_90,B_88,D_91),k1_relset_1(B_88,C_92,E_89))
      | ~ m1_subset_1(E_89,k1_zfmisc_1(k2_zfmisc_1(B_88,C_92)))
      | ~ v1_funct_1(E_89)
      | ~ m1_subset_1(D_91,k1_zfmisc_1(k2_zfmisc_1(A_90,B_88)))
      | ~ v1_funct_2(D_91,A_90,B_88)
      | ~ v1_funct_1(D_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_215,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_2','#skF_5','#skF_6') = k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2')))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_212])).

tff(c_218,plain,
    ( k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_32,c_142,c_215])).

tff(c_219,plain,(
    k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_201,c_218])).

tff(c_24,plain,(
    k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_220,plain,(
    k1_funct_1(k5_relat_1('#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_24])).

tff(c_244,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ m1_subset_1('#skF_7','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_220])).

tff(c_259,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_75,c_34,c_244])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:50:54 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.37/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.37  
% 2.37/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.37  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 2.37/1.37  
% 2.37/1.37  %Foreground sorts:
% 2.37/1.37  
% 2.37/1.37  
% 2.37/1.37  %Background operators:
% 2.37/1.37  
% 2.37/1.37  
% 2.37/1.37  %Foreground operators:
% 2.37/1.37  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.37/1.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.37/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.37/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.37/1.37  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.37/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.37/1.37  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.37/1.37  tff('#skF_7', type, '#skF_7': $i).
% 2.37/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.37/1.37  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.37/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.37/1.37  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.37/1.37  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 2.37/1.37  tff('#skF_6', type, '#skF_6': $i).
% 2.37/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.37/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.37/1.37  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.37/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.37/1.37  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.37/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.37/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.37/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.37/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.37/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.37/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.37/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.37/1.37  
% 2.37/1.39  tff(f_126, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 2.37/1.39  tff(f_52, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.37/1.39  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.37/1.39  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.37/1.39  tff(f_101, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_relat_1(E) & v1_funct_1(E)) => (r2_hidden(C, A) => ((B = k1_xboole_0) | (k1_funct_1(k5_relat_1(D, E), C) = k1_funct_1(E, k1_funct_1(D, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_funct_2)).
% 2.37/1.39  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.37/1.39  tff(f_37, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.37/1.39  tff(f_57, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.37/1.39  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.37/1.39  tff(f_84, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 2.37/1.39  tff(f_74, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (r1_tarski(k2_relset_1(A, B, D), k1_relset_1(B, C, E)) => ((B = k1_xboole_0) | (k8_funct_2(A, B, C, D, E) = k1_partfun1(A, B, B, C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_2)).
% 2.37/1.39  tff(c_30, plain, (m1_subset_1('#skF_7', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.37/1.39  tff(c_14, plain, (![A_12, B_13]: (v1_relat_1(k2_zfmisc_1(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.37/1.39  tff(c_32, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.37/1.39  tff(c_63, plain, (![B_55, A_56]: (v1_relat_1(B_55) | ~m1_subset_1(B_55, k1_zfmisc_1(A_56)) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.37/1.39  tff(c_69, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_63])).
% 2.37/1.39  tff(c_75, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_69])).
% 2.37/1.39  tff(c_34, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.37/1.39  tff(c_26, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.37/1.39  tff(c_40, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.37/1.39  tff(c_38, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.37/1.39  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.37/1.39  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.37/1.39  tff(c_154, plain, (![D_77, B_75, C_74, E_76, A_73]: (k1_funct_1(k5_relat_1(D_77, E_76), C_74)=k1_funct_1(E_76, k1_funct_1(D_77, C_74)) | k1_xboole_0=B_75 | ~r2_hidden(C_74, A_73) | ~v1_funct_1(E_76) | ~v1_relat_1(E_76) | ~m1_subset_1(D_77, k1_zfmisc_1(k2_zfmisc_1(A_73, B_75))) | ~v1_funct_2(D_77, A_73, B_75) | ~v1_funct_1(D_77))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.37/1.39  tff(c_161, plain, (![D_78, E_79, A_80, B_81]: (k1_funct_1(k5_relat_1(D_78, E_79), '#skF_1'(A_80))=k1_funct_1(E_79, k1_funct_1(D_78, '#skF_1'(A_80))) | k1_xboole_0=B_81 | ~v1_funct_1(E_79) | ~v1_relat_1(E_79) | ~m1_subset_1(D_78, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))) | ~v1_funct_2(D_78, A_80, B_81) | ~v1_funct_1(D_78) | v1_xboole_0(A_80))), inference(resolution, [status(thm)], [c_4, c_154])).
% 2.37/1.39  tff(c_163, plain, (![E_79]: (k1_funct_1(k5_relat_1('#skF_5', E_79), '#skF_1'('#skF_3'))=k1_funct_1(E_79, k1_funct_1('#skF_5', '#skF_1'('#skF_3'))) | k1_xboole_0='#skF_4' | ~v1_funct_1(E_79) | ~v1_relat_1(E_79) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_36, c_161])).
% 2.37/1.39  tff(c_168, plain, (![E_79]: (k1_funct_1(k5_relat_1('#skF_5', E_79), '#skF_1'('#skF_3'))=k1_funct_1(E_79, k1_funct_1('#skF_5', '#skF_1'('#skF_3'))) | k1_xboole_0='#skF_4' | ~v1_funct_1(E_79) | ~v1_relat_1(E_79) | v1_xboole_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_163])).
% 2.37/1.39  tff(c_173, plain, (v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_168])).
% 2.37/1.39  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.37/1.39  tff(c_183, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_173, c_6])).
% 2.37/1.39  tff(c_187, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_183])).
% 2.37/1.39  tff(c_189, plain, (~v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_168])).
% 2.37/1.39  tff(c_42, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.37/1.39  tff(c_188, plain, (![E_79]: (k1_xboole_0='#skF_4' | k1_funct_1(k5_relat_1('#skF_5', E_79), '#skF_1'('#skF_3'))=k1_funct_1(E_79, k1_funct_1('#skF_5', '#skF_1'('#skF_3'))) | ~v1_funct_1(E_79) | ~v1_relat_1(E_79))), inference(splitRight, [status(thm)], [c_168])).
% 2.37/1.39  tff(c_190, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_188])).
% 2.37/1.39  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.37/1.39  tff(c_52, plain, (![B_52, A_53]: (~r1_tarski(B_52, A_53) | ~r2_hidden(A_53, B_52))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.37/1.39  tff(c_57, plain, (![A_54]: (~r1_tarski(A_54, '#skF_1'(A_54)) | v1_xboole_0(A_54))), inference(resolution, [status(thm)], [c_4, c_52])).
% 2.37/1.39  tff(c_62, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_57])).
% 2.37/1.39  tff(c_194, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_190, c_62])).
% 2.37/1.39  tff(c_199, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_194])).
% 2.37/1.39  tff(c_201, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_188])).
% 2.37/1.39  tff(c_10, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.37/1.39  tff(c_225, plain, (![A_95, B_96, D_94, B_93, E_97]: (k1_funct_1(k5_relat_1(D_94, E_97), A_95)=k1_funct_1(E_97, k1_funct_1(D_94, A_95)) | k1_xboole_0=B_96 | ~v1_funct_1(E_97) | ~v1_relat_1(E_97) | ~m1_subset_1(D_94, k1_zfmisc_1(k2_zfmisc_1(B_93, B_96))) | ~v1_funct_2(D_94, B_93, B_96) | ~v1_funct_1(D_94) | v1_xboole_0(B_93) | ~m1_subset_1(A_95, B_93))), inference(resolution, [status(thm)], [c_10, c_154])).
% 2.37/1.39  tff(c_227, plain, (![E_97, A_95]: (k1_funct_1(k5_relat_1('#skF_5', E_97), A_95)=k1_funct_1(E_97, k1_funct_1('#skF_5', A_95)) | k1_xboole_0='#skF_4' | ~v1_funct_1(E_97) | ~v1_relat_1(E_97) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_3') | ~m1_subset_1(A_95, '#skF_3'))), inference(resolution, [status(thm)], [c_36, c_225])).
% 2.37/1.39  tff(c_232, plain, (![E_97, A_95]: (k1_funct_1(k5_relat_1('#skF_5', E_97), A_95)=k1_funct_1(E_97, k1_funct_1('#skF_5', A_95)) | k1_xboole_0='#skF_4' | ~v1_funct_1(E_97) | ~v1_relat_1(E_97) | v1_xboole_0('#skF_3') | ~m1_subset_1(A_95, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_227])).
% 2.37/1.39  tff(c_238, plain, (![E_98, A_99]: (k1_funct_1(k5_relat_1('#skF_5', E_98), A_99)=k1_funct_1(E_98, k1_funct_1('#skF_5', A_99)) | ~v1_funct_1(E_98) | ~v1_relat_1(E_98) | ~m1_subset_1(A_99, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_189, c_201, c_232])).
% 2.37/1.39  tff(c_101, plain, (![B_66, A_61, F_64, C_62, E_63, D_65]: (k1_partfun1(A_61, B_66, C_62, D_65, E_63, F_64)=k5_relat_1(E_63, F_64) | ~m1_subset_1(F_64, k1_zfmisc_1(k2_zfmisc_1(C_62, D_65))) | ~v1_funct_1(F_64) | ~m1_subset_1(E_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_66))) | ~v1_funct_1(E_63))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.37/1.39  tff(c_105, plain, (![A_61, B_66, E_63]: (k1_partfun1(A_61, B_66, '#skF_4', '#skF_2', E_63, '#skF_6')=k5_relat_1(E_63, '#skF_6') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_66))) | ~v1_funct_1(E_63))), inference(resolution, [status(thm)], [c_32, c_101])).
% 2.37/1.39  tff(c_133, plain, (![A_70, B_71, E_72]: (k1_partfun1(A_70, B_71, '#skF_4', '#skF_2', E_72, '#skF_6')=k5_relat_1(E_72, '#skF_6') | ~m1_subset_1(E_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))) | ~v1_funct_1(E_72))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_105])).
% 2.37/1.39  tff(c_136, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_36, c_133])).
% 2.37/1.39  tff(c_142, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_136])).
% 2.37/1.39  tff(c_28, plain, (r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), k1_relset_1('#skF_4', '#skF_2', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.37/1.39  tff(c_212, plain, (![C_92, B_88, D_91, E_89, A_90]: (k1_partfun1(A_90, B_88, B_88, C_92, D_91, E_89)=k8_funct_2(A_90, B_88, C_92, D_91, E_89) | k1_xboole_0=B_88 | ~r1_tarski(k2_relset_1(A_90, B_88, D_91), k1_relset_1(B_88, C_92, E_89)) | ~m1_subset_1(E_89, k1_zfmisc_1(k2_zfmisc_1(B_88, C_92))) | ~v1_funct_1(E_89) | ~m1_subset_1(D_91, k1_zfmisc_1(k2_zfmisc_1(A_90, B_88))) | ~v1_funct_2(D_91, A_90, B_88) | ~v1_funct_1(D_91))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.37/1.39  tff(c_215, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_28, c_212])).
% 2.37/1.39  tff(c_218, plain, (k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_32, c_142, c_215])).
% 2.37/1.39  tff(c_219, plain, (k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_201, c_218])).
% 2.37/1.39  tff(c_24, plain, (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.37/1.39  tff(c_220, plain, (k1_funct_1(k5_relat_1('#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_219, c_24])).
% 2.37/1.39  tff(c_244, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~m1_subset_1('#skF_7', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_238, c_220])).
% 2.37/1.39  tff(c_259, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_75, c_34, c_244])).
% 2.37/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.39  
% 2.37/1.39  Inference rules
% 2.37/1.39  ----------------------
% 2.37/1.39  #Ref     : 0
% 2.37/1.39  #Sup     : 42
% 2.37/1.39  #Fact    : 0
% 2.37/1.39  #Define  : 0
% 2.37/1.39  #Split   : 5
% 2.37/1.39  #Chain   : 0
% 2.37/1.39  #Close   : 0
% 2.37/1.39  
% 2.37/1.39  Ordering : KBO
% 2.37/1.39  
% 2.37/1.39  Simplification rules
% 2.37/1.39  ----------------------
% 2.37/1.39  #Subsume      : 1
% 2.37/1.39  #Demod        : 37
% 2.37/1.39  #Tautology    : 17
% 2.37/1.39  #SimpNegUnit  : 6
% 2.37/1.39  #BackRed      : 7
% 2.37/1.39  
% 2.37/1.39  #Partial instantiations: 0
% 2.37/1.39  #Strategies tried      : 1
% 2.37/1.39  
% 2.37/1.39  Timing (in seconds)
% 2.37/1.39  ----------------------
% 2.37/1.39  Preprocessing        : 0.35
% 2.37/1.39  Parsing              : 0.19
% 2.37/1.39  CNF conversion       : 0.03
% 2.37/1.39  Main loop            : 0.23
% 2.37/1.39  Inferencing          : 0.09
% 2.37/1.39  Reduction            : 0.07
% 2.37/1.39  Demodulation         : 0.05
% 2.37/1.39  BG Simplification    : 0.02
% 2.37/1.39  Subsumption          : 0.04
% 2.37/1.39  Abstraction          : 0.01
% 2.37/1.39  MUC search           : 0.00
% 2.37/1.39  Cooper               : 0.00
% 2.37/1.39  Total                : 0.61
% 2.37/1.39  Index Insertion      : 0.00
% 2.37/1.39  Index Deletion       : 0.00
% 2.37/1.39  Index Matching       : 0.00
% 2.69/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
