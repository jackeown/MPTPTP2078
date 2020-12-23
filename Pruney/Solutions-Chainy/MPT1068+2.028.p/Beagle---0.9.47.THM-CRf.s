%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:44 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 174 expanded)
%              Number of leaves         :   34 (  80 expanded)
%              Depth                    :   10
%              Number of atoms          :  158 ( 696 expanded)
%              Number of equality atoms :   38 ( 146 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

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
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

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

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_30,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_16,plain,(
    ! [A_7,B_8] : v1_relat_1(k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_72,plain,(
    ! [B_47,A_48] :
      ( v1_relat_1(B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_48))
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_79,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_32,c_72])).

tff(c_86,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_79])).

tff(c_34,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_42,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_40,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_38,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_97,plain,(
    ! [A_57,C_52,D_53,F_55,E_56,B_54] :
      ( k1_partfun1(A_57,B_54,C_52,D_53,E_56,F_55) = k5_relat_1(E_56,F_55)
      | ~ m1_subset_1(F_55,k1_zfmisc_1(k2_zfmisc_1(C_52,D_53)))
      | ~ v1_funct_1(F_55)
      | ~ m1_subset_1(E_56,k1_zfmisc_1(k2_zfmisc_1(A_57,B_54)))
      | ~ v1_funct_1(E_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_102,plain,(
    ! [A_57,B_54,E_56] :
      ( k1_partfun1(A_57,B_54,'#skF_3','#skF_1',E_56,'#skF_5') = k5_relat_1(E_56,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_56,k1_zfmisc_1(k2_zfmisc_1(A_57,B_54)))
      | ~ v1_funct_1(E_56) ) ),
    inference(resolution,[status(thm)],[c_32,c_97])).

tff(c_112,plain,(
    ! [A_58,B_59,E_60] :
      ( k1_partfun1(A_58,B_59,'#skF_3','#skF_1',E_60,'#skF_5') = k5_relat_1(E_60,'#skF_5')
      | ~ m1_subset_1(E_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59)))
      | ~ v1_funct_1(E_60) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_102])).

tff(c_122,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_112])).

tff(c_129,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_122])).

tff(c_28,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_relset_1('#skF_3','#skF_1','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_221,plain,(
    ! [B_98,A_102,E_99,D_101,C_100] :
      ( k1_partfun1(A_102,B_98,B_98,C_100,D_101,E_99) = k8_funct_2(A_102,B_98,C_100,D_101,E_99)
      | k1_xboole_0 = B_98
      | ~ r1_tarski(k2_relset_1(A_102,B_98,D_101),k1_relset_1(B_98,C_100,E_99))
      | ~ m1_subset_1(E_99,k1_zfmisc_1(k2_zfmisc_1(B_98,C_100)))
      | ~ v1_funct_1(E_99)
      | ~ m1_subset_1(D_101,k1_zfmisc_1(k2_zfmisc_1(A_102,B_98)))
      | ~ v1_funct_2(D_101,A_102,B_98)
      | ~ v1_funct_1(D_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_224,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5')
    | k1_xboole_0 = '#skF_3'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_221])).

tff(c_227,plain,
    ( k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_32,c_129,c_224])).

tff(c_228,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_227])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_234,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_2])).

tff(c_237,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_234])).

tff(c_239,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_227])).

tff(c_50,plain,(
    ! [B_41,A_42] :
      ( v1_xboole_0(B_41)
      | ~ m1_subset_1(B_41,A_42)
      | ~ v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_62,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_50])).

tff(c_63,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_8,plain,(
    ! [B_3,A_2] :
      ( r2_hidden(B_3,A_2)
      | ~ m1_subset_1(B_3,A_2)
      | v1_xboole_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_164,plain,(
    ! [E_66,C_67,B_68,D_65,A_64] :
      ( k1_funct_1(k5_relat_1(D_65,E_66),C_67) = k1_funct_1(E_66,k1_funct_1(D_65,C_67))
      | k1_xboole_0 = B_68
      | ~ r2_hidden(C_67,A_64)
      | ~ v1_funct_1(E_66)
      | ~ v1_relat_1(E_66)
      | ~ m1_subset_1(D_65,k1_zfmisc_1(k2_zfmisc_1(A_64,B_68)))
      | ~ v1_funct_2(D_65,A_64,B_68)
      | ~ v1_funct_1(D_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_204,plain,(
    ! [A_96,E_94,B_95,D_97,B_93] :
      ( k1_funct_1(k5_relat_1(D_97,E_94),B_95) = k1_funct_1(E_94,k1_funct_1(D_97,B_95))
      | k1_xboole_0 = B_93
      | ~ v1_funct_1(E_94)
      | ~ v1_relat_1(E_94)
      | ~ m1_subset_1(D_97,k1_zfmisc_1(k2_zfmisc_1(A_96,B_93)))
      | ~ v1_funct_2(D_97,A_96,B_93)
      | ~ v1_funct_1(D_97)
      | ~ m1_subset_1(B_95,A_96)
      | v1_xboole_0(A_96) ) ),
    inference(resolution,[status(thm)],[c_8,c_164])).

tff(c_211,plain,(
    ! [E_94,B_95] :
      ( k1_funct_1(k5_relat_1('#skF_4',E_94),B_95) = k1_funct_1(E_94,k1_funct_1('#skF_4',B_95))
      | k1_xboole_0 = '#skF_3'
      | ~ v1_funct_1(E_94)
      | ~ v1_relat_1(E_94)
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(B_95,'#skF_2')
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_36,c_204])).

tff(c_219,plain,(
    ! [E_94,B_95] :
      ( k1_funct_1(k5_relat_1('#skF_4',E_94),B_95) = k1_funct_1(E_94,k1_funct_1('#skF_4',B_95))
      | k1_xboole_0 = '#skF_3'
      | ~ v1_funct_1(E_94)
      | ~ v1_relat_1(E_94)
      | ~ m1_subset_1(B_95,'#skF_2')
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_211])).

tff(c_220,plain,(
    ! [E_94,B_95] :
      ( k1_funct_1(k5_relat_1('#skF_4',E_94),B_95) = k1_funct_1(E_94,k1_funct_1('#skF_4',B_95))
      | k1_xboole_0 = '#skF_3'
      | ~ v1_funct_1(E_94)
      | ~ v1_relat_1(E_94)
      | ~ m1_subset_1(B_95,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_219])).

tff(c_247,plain,(
    ! [E_103,B_104] :
      ( k1_funct_1(k5_relat_1('#skF_4',E_103),B_104) = k1_funct_1(E_103,k1_funct_1('#skF_4',B_104))
      | ~ v1_funct_1(E_103)
      | ~ v1_relat_1(E_103)
      | ~ m1_subset_1(B_104,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_239,c_220])).

tff(c_238,plain,(
    k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_227])).

tff(c_24,plain,(
    k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_241,plain,(
    k1_funct_1(k5_relat_1('#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_24])).

tff(c_253,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_241])).

tff(c_261,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_86,c_34,c_253])).

tff(c_263,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_275,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_263,c_4])).

tff(c_279,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_275])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:04:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.32  
% 2.59/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.32  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.59/1.32  
% 2.59/1.32  %Foreground sorts:
% 2.59/1.32  
% 2.59/1.32  
% 2.59/1.32  %Background operators:
% 2.59/1.32  
% 2.59/1.32  
% 2.59/1.32  %Foreground operators:
% 2.59/1.32  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.59/1.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.59/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.59/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.59/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.59/1.32  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.59/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.59/1.32  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.59/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.59/1.32  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.59/1.32  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 2.59/1.32  tff('#skF_6', type, '#skF_6': $i).
% 2.59/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.59/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.59/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.59/1.32  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.59/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.59/1.32  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.59/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.59/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.59/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.59/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.59/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.59/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.59/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.59/1.32  
% 2.59/1.34  tff(f_121, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 2.59/1.34  tff(f_52, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.59/1.34  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.59/1.34  tff(f_79, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 2.59/1.34  tff(f_69, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (r1_tarski(k2_relset_1(A, B, D), k1_relset_1(B, C, E)) => ((B = k1_xboole_0) | (k8_funct_2(A, B, C, D, E) = k1_partfun1(A, B, B, C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_2)).
% 2.59/1.34  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.59/1.34  tff(f_43, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.59/1.34  tff(f_96, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_relat_1(E) & v1_funct_1(E)) => (r2_hidden(C, A) => ((B = k1_xboole_0) | (k1_funct_1(k5_relat_1(D, E), C) = k1_funct_1(E, k1_funct_1(D, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_funct_2)).
% 2.59/1.34  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.59/1.34  tff(c_26, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.59/1.34  tff(c_30, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.59/1.34  tff(c_16, plain, (![A_7, B_8]: (v1_relat_1(k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.59/1.34  tff(c_32, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.59/1.34  tff(c_72, plain, (![B_47, A_48]: (v1_relat_1(B_47) | ~m1_subset_1(B_47, k1_zfmisc_1(A_48)) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.59/1.34  tff(c_79, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_32, c_72])).
% 2.59/1.34  tff(c_86, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_79])).
% 2.59/1.34  tff(c_34, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.59/1.34  tff(c_42, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.59/1.34  tff(c_40, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.59/1.34  tff(c_38, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.59/1.34  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.59/1.34  tff(c_97, plain, (![A_57, C_52, D_53, F_55, E_56, B_54]: (k1_partfun1(A_57, B_54, C_52, D_53, E_56, F_55)=k5_relat_1(E_56, F_55) | ~m1_subset_1(F_55, k1_zfmisc_1(k2_zfmisc_1(C_52, D_53))) | ~v1_funct_1(F_55) | ~m1_subset_1(E_56, k1_zfmisc_1(k2_zfmisc_1(A_57, B_54))) | ~v1_funct_1(E_56))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.59/1.34  tff(c_102, plain, (![A_57, B_54, E_56]: (k1_partfun1(A_57, B_54, '#skF_3', '#skF_1', E_56, '#skF_5')=k5_relat_1(E_56, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_56, k1_zfmisc_1(k2_zfmisc_1(A_57, B_54))) | ~v1_funct_1(E_56))), inference(resolution, [status(thm)], [c_32, c_97])).
% 2.59/1.34  tff(c_112, plain, (![A_58, B_59, E_60]: (k1_partfun1(A_58, B_59, '#skF_3', '#skF_1', E_60, '#skF_5')=k5_relat_1(E_60, '#skF_5') | ~m1_subset_1(E_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))) | ~v1_funct_1(E_60))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_102])).
% 2.59/1.34  tff(c_122, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_112])).
% 2.59/1.34  tff(c_129, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_122])).
% 2.59/1.34  tff(c_28, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_relset_1('#skF_3', '#skF_1', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.59/1.34  tff(c_221, plain, (![B_98, A_102, E_99, D_101, C_100]: (k1_partfun1(A_102, B_98, B_98, C_100, D_101, E_99)=k8_funct_2(A_102, B_98, C_100, D_101, E_99) | k1_xboole_0=B_98 | ~r1_tarski(k2_relset_1(A_102, B_98, D_101), k1_relset_1(B_98, C_100, E_99)) | ~m1_subset_1(E_99, k1_zfmisc_1(k2_zfmisc_1(B_98, C_100))) | ~v1_funct_1(E_99) | ~m1_subset_1(D_101, k1_zfmisc_1(k2_zfmisc_1(A_102, B_98))) | ~v1_funct_2(D_101, A_102, B_98) | ~v1_funct_1(D_101))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.59/1.34  tff(c_224, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5') | k1_xboole_0='#skF_3' | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_221])).
% 2.59/1.34  tff(c_227, plain, (k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_32, c_129, c_224])).
% 2.59/1.34  tff(c_228, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_227])).
% 2.59/1.34  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.59/1.34  tff(c_234, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_228, c_2])).
% 2.59/1.34  tff(c_237, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_234])).
% 2.59/1.34  tff(c_239, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_227])).
% 2.59/1.34  tff(c_50, plain, (![B_41, A_42]: (v1_xboole_0(B_41) | ~m1_subset_1(B_41, A_42) | ~v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.59/1.34  tff(c_62, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_30, c_50])).
% 2.59/1.34  tff(c_63, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_62])).
% 2.59/1.34  tff(c_8, plain, (![B_3, A_2]: (r2_hidden(B_3, A_2) | ~m1_subset_1(B_3, A_2) | v1_xboole_0(A_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.59/1.34  tff(c_164, plain, (![E_66, C_67, B_68, D_65, A_64]: (k1_funct_1(k5_relat_1(D_65, E_66), C_67)=k1_funct_1(E_66, k1_funct_1(D_65, C_67)) | k1_xboole_0=B_68 | ~r2_hidden(C_67, A_64) | ~v1_funct_1(E_66) | ~v1_relat_1(E_66) | ~m1_subset_1(D_65, k1_zfmisc_1(k2_zfmisc_1(A_64, B_68))) | ~v1_funct_2(D_65, A_64, B_68) | ~v1_funct_1(D_65))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.59/1.34  tff(c_204, plain, (![A_96, E_94, B_95, D_97, B_93]: (k1_funct_1(k5_relat_1(D_97, E_94), B_95)=k1_funct_1(E_94, k1_funct_1(D_97, B_95)) | k1_xboole_0=B_93 | ~v1_funct_1(E_94) | ~v1_relat_1(E_94) | ~m1_subset_1(D_97, k1_zfmisc_1(k2_zfmisc_1(A_96, B_93))) | ~v1_funct_2(D_97, A_96, B_93) | ~v1_funct_1(D_97) | ~m1_subset_1(B_95, A_96) | v1_xboole_0(A_96))), inference(resolution, [status(thm)], [c_8, c_164])).
% 2.59/1.34  tff(c_211, plain, (![E_94, B_95]: (k1_funct_1(k5_relat_1('#skF_4', E_94), B_95)=k1_funct_1(E_94, k1_funct_1('#skF_4', B_95)) | k1_xboole_0='#skF_3' | ~v1_funct_1(E_94) | ~v1_relat_1(E_94) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1(B_95, '#skF_2') | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_36, c_204])).
% 2.59/1.34  tff(c_219, plain, (![E_94, B_95]: (k1_funct_1(k5_relat_1('#skF_4', E_94), B_95)=k1_funct_1(E_94, k1_funct_1('#skF_4', B_95)) | k1_xboole_0='#skF_3' | ~v1_funct_1(E_94) | ~v1_relat_1(E_94) | ~m1_subset_1(B_95, '#skF_2') | v1_xboole_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_211])).
% 2.59/1.34  tff(c_220, plain, (![E_94, B_95]: (k1_funct_1(k5_relat_1('#skF_4', E_94), B_95)=k1_funct_1(E_94, k1_funct_1('#skF_4', B_95)) | k1_xboole_0='#skF_3' | ~v1_funct_1(E_94) | ~v1_relat_1(E_94) | ~m1_subset_1(B_95, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_63, c_219])).
% 2.59/1.34  tff(c_247, plain, (![E_103, B_104]: (k1_funct_1(k5_relat_1('#skF_4', E_103), B_104)=k1_funct_1(E_103, k1_funct_1('#skF_4', B_104)) | ~v1_funct_1(E_103) | ~v1_relat_1(E_103) | ~m1_subset_1(B_104, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_239, c_220])).
% 2.59/1.34  tff(c_238, plain, (k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_227])).
% 2.59/1.34  tff(c_24, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.59/1.34  tff(c_241, plain, (k1_funct_1(k5_relat_1('#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_238, c_24])).
% 2.59/1.34  tff(c_253, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_247, c_241])).
% 2.59/1.34  tff(c_261, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_86, c_34, c_253])).
% 2.59/1.34  tff(c_263, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_62])).
% 2.59/1.34  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.59/1.34  tff(c_275, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_263, c_4])).
% 2.59/1.34  tff(c_279, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_275])).
% 2.59/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.34  
% 2.59/1.34  Inference rules
% 2.59/1.34  ----------------------
% 2.59/1.34  #Ref     : 0
% 2.59/1.34  #Sup     : 47
% 2.59/1.34  #Fact    : 0
% 2.59/1.34  #Define  : 0
% 2.59/1.34  #Split   : 7
% 2.59/1.34  #Chain   : 0
% 2.59/1.34  #Close   : 0
% 2.59/1.34  
% 2.59/1.34  Ordering : KBO
% 2.59/1.34  
% 2.59/1.34  Simplification rules
% 2.59/1.34  ----------------------
% 2.59/1.34  #Subsume      : 4
% 2.59/1.34  #Demod        : 30
% 2.59/1.34  #Tautology    : 15
% 2.59/1.34  #SimpNegUnit  : 5
% 2.59/1.34  #BackRed      : 8
% 2.59/1.34  
% 2.59/1.34  #Partial instantiations: 0
% 2.59/1.34  #Strategies tried      : 1
% 2.59/1.34  
% 2.59/1.34  Timing (in seconds)
% 2.59/1.34  ----------------------
% 2.59/1.34  Preprocessing        : 0.32
% 2.59/1.34  Parsing              : 0.17
% 2.59/1.34  CNF conversion       : 0.02
% 2.59/1.34  Main loop            : 0.25
% 2.59/1.34  Inferencing          : 0.09
% 2.59/1.34  Reduction            : 0.07
% 2.59/1.35  Demodulation         : 0.05
% 2.59/1.35  BG Simplification    : 0.02
% 2.59/1.35  Subsumption          : 0.05
% 2.59/1.35  Abstraction          : 0.01
% 2.59/1.35  MUC search           : 0.00
% 2.59/1.35  Cooper               : 0.00
% 2.59/1.35  Total                : 0.61
% 2.59/1.35  Index Insertion      : 0.00
% 2.59/1.35  Index Deletion       : 0.00
% 2.59/1.35  Index Matching       : 0.00
% 2.59/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
