%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:48 EST 2020

% Result     : Theorem 3.24s
% Output     : CNFRefutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 402 expanded)
%              Number of leaves         :   42 ( 158 expanded)
%              Depth                    :   17
%              Number of atoms          :  278 (1621 expanded)
%              Number of equality atoms :   58 ( 316 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_partfun1,type,(
    k7_partfun1: ( $i * $i * $i ) > $i )).

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_172,negated_conjecture,(
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
                        | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k7_partfun1(A,E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_116,axiom,(
    ! [A,B,C] :
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
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_xboole_0(B) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ~ v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_partfun1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_128,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_147,axiom,(
    ! [A,B,C,D] :
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

tff(f_92,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_64,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_52,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_62,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_60,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_155,plain,(
    ! [A_86,B_87,C_88] :
      ( k1_relset_1(A_86,B_87,C_88) = k1_relat_1(C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_168,plain,(
    k1_relset_1('#skF_3','#skF_1','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_155])).

tff(c_50,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_relset_1('#skF_3','#skF_1','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_170,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_50])).

tff(c_56,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_580,plain,(
    ! [E_166,C_165,F_167,A_169,B_168,D_164] :
      ( k1_funct_1(k8_funct_2(B_168,C_165,A_169,D_164,E_166),F_167) = k1_funct_1(E_166,k1_funct_1(D_164,F_167))
      | k1_xboole_0 = B_168
      | ~ r1_tarski(k2_relset_1(B_168,C_165,D_164),k1_relset_1(C_165,A_169,E_166))
      | ~ m1_subset_1(F_167,B_168)
      | ~ m1_subset_1(E_166,k1_zfmisc_1(k2_zfmisc_1(C_165,A_169)))
      | ~ v1_funct_1(E_166)
      | ~ m1_subset_1(D_164,k1_zfmisc_1(k2_zfmisc_1(B_168,C_165)))
      | ~ v1_funct_2(D_164,B_168,C_165)
      | ~ v1_funct_1(D_164)
      | v1_xboole_0(C_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_586,plain,(
    ! [B_168,D_164,F_167] :
      ( k1_funct_1(k8_funct_2(B_168,'#skF_3','#skF_1',D_164,'#skF_5'),F_167) = k1_funct_1('#skF_5',k1_funct_1(D_164,F_167))
      | k1_xboole_0 = B_168
      | ~ r1_tarski(k2_relset_1(B_168,'#skF_3',D_164),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(F_167,B_168)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_164,k1_zfmisc_1(k2_zfmisc_1(B_168,'#skF_3')))
      | ~ v1_funct_2(D_164,B_168,'#skF_3')
      | ~ v1_funct_1(D_164)
      | v1_xboole_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_580])).

tff(c_594,plain,(
    ! [B_168,D_164,F_167] :
      ( k1_funct_1(k8_funct_2(B_168,'#skF_3','#skF_1',D_164,'#skF_5'),F_167) = k1_funct_1('#skF_5',k1_funct_1(D_164,F_167))
      | k1_xboole_0 = B_168
      | ~ r1_tarski(k2_relset_1(B_168,'#skF_3',D_164),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(F_167,B_168)
      | ~ m1_subset_1(D_164,k1_zfmisc_1(k2_zfmisc_1(B_168,'#skF_3')))
      | ~ v1_funct_2(D_164,B_168,'#skF_3')
      | ~ v1_funct_1(D_164)
      | v1_xboole_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_586])).

tff(c_601,plain,(
    ! [B_173,D_174,F_175] :
      ( k1_funct_1(k8_funct_2(B_173,'#skF_3','#skF_1',D_174,'#skF_5'),F_175) = k1_funct_1('#skF_5',k1_funct_1(D_174,F_175))
      | k1_xboole_0 = B_173
      | ~ r1_tarski(k2_relset_1(B_173,'#skF_3',D_174),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(F_175,B_173)
      | ~ m1_subset_1(D_174,k1_zfmisc_1(k2_zfmisc_1(B_173,'#skF_3')))
      | ~ v1_funct_2(D_174,B_173,'#skF_3')
      | ~ v1_funct_1(D_174) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_594])).

tff(c_603,plain,(
    ! [F_175] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),F_175) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_175))
      | k1_xboole_0 = '#skF_2'
      | ~ m1_subset_1(F_175,'#skF_2')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_170,c_601])).

tff(c_606,plain,(
    ! [F_175] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),F_175) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_175))
      | k1_xboole_0 = '#skF_2'
      | ~ m1_subset_1(F_175,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_603])).

tff(c_608,plain,(
    ! [F_176] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),F_176) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_176))
      | ~ m1_subset_1(F_176,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_606])).

tff(c_121,plain,(
    ! [C_74,B_75,A_76] :
      ( v5_relat_1(C_74,B_75)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_76,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_134,plain,(
    v5_relat_1('#skF_5','#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_121])).

tff(c_95,plain,(
    ! [C_66,A_67,B_68] :
      ( v1_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_106,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_95])).

tff(c_201,plain,(
    ! [C_94,A_95,B_96] :
      ( v1_partfun1(C_94,A_95)
      | ~ v1_funct_2(C_94,A_95,B_96)
      | ~ v1_funct_1(C_94)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96)))
      | v1_xboole_0(B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_210,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_201])).

tff(c_220,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_210])).

tff(c_221,plain,(
    v1_partfun1('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_220])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_8,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_179,plain,(
    ! [C_89,A_90,B_91] :
      ( ~ v1_partfun1(C_89,A_90)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91)))
      | ~ v1_xboole_0(B_91)
      | v1_xboole_0(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_191,plain,(
    ! [C_89,A_2] :
      ( ~ v1_partfun1(C_89,A_2)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0)
      | v1_xboole_0(A_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_179])).

tff(c_198,plain,(
    ! [C_89,A_2] :
      ( ~ v1_partfun1(C_89,A_2)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k1_xboole_0))
      | v1_xboole_0(A_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_191])).

tff(c_225,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_221,c_198])).

tff(c_226,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_225])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( r2_hidden(A_4,B_5)
      | v1_xboole_0(B_5)
      | ~ m1_subset_1(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_236,plain,(
    ! [D_106,C_107,B_108,A_109] :
      ( r2_hidden(k1_funct_1(D_106,C_107),B_108)
      | k1_xboole_0 = B_108
      | ~ r2_hidden(C_107,A_109)
      | ~ m1_subset_1(D_106,k1_zfmisc_1(k2_zfmisc_1(A_109,B_108)))
      | ~ v1_funct_2(D_106,A_109,B_108)
      | ~ v1_funct_1(D_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_349,plain,(
    ! [D_127,A_128,B_129,B_130] :
      ( r2_hidden(k1_funct_1(D_127,A_128),B_129)
      | k1_xboole_0 = B_129
      | ~ m1_subset_1(D_127,k1_zfmisc_1(k2_zfmisc_1(B_130,B_129)))
      | ~ v1_funct_2(D_127,B_130,B_129)
      | ~ v1_funct_1(D_127)
      | v1_xboole_0(B_130)
      | ~ m1_subset_1(A_128,B_130) ) ),
    inference(resolution,[status(thm)],[c_12,c_236])).

tff(c_355,plain,(
    ! [A_128] :
      ( r2_hidden(k1_funct_1('#skF_4',A_128),'#skF_3')
      | k1_xboole_0 = '#skF_3'
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_128,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_58,c_349])).

tff(c_365,plain,(
    ! [A_128] :
      ( r2_hidden(k1_funct_1('#skF_4',A_128),'#skF_3')
      | k1_xboole_0 = '#skF_3'
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_128,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_355])).

tff(c_367,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_365])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_370,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_367,c_4])).

tff(c_374,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_370])).

tff(c_376,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_365])).

tff(c_268,plain,(
    ! [B_116,D_117,A_118,C_119] :
      ( k1_xboole_0 = B_116
      | v1_funct_2(D_117,A_118,C_119)
      | ~ r1_tarski(k2_relset_1(A_118,B_116,D_117),C_119)
      | ~ m1_subset_1(D_117,k1_zfmisc_1(k2_zfmisc_1(A_118,B_116)))
      | ~ v1_funct_2(D_117,A_118,B_116)
      | ~ v1_funct_1(D_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_270,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4','#skF_2',k1_relat_1('#skF_5'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_170,c_268])).

tff(c_273,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4','#skF_2',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_270])).

tff(c_278,plain,(
    v1_funct_2('#skF_4','#skF_2',k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_273])).

tff(c_375,plain,(
    ! [A_128] :
      ( k1_xboole_0 = '#skF_3'
      | r2_hidden(k1_funct_1('#skF_4',A_128),'#skF_3')
      | ~ m1_subset_1(A_128,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_365])).

tff(c_377,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_375])).

tff(c_404,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_377,c_2])).

tff(c_407,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_404])).

tff(c_409,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_375])).

tff(c_428,plain,(
    ! [B_139,D_140,A_141,C_142] :
      ( k1_xboole_0 = B_139
      | m1_subset_1(D_140,k1_zfmisc_1(k2_zfmisc_1(A_141,C_142)))
      | ~ r1_tarski(k2_relset_1(A_141,B_139,D_140),C_142)
      | ~ m1_subset_1(D_140,k1_zfmisc_1(k2_zfmisc_1(A_141,B_139)))
      | ~ v1_funct_2(D_140,A_141,B_139)
      | ~ v1_funct_1(D_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_430,plain,
    ( k1_xboole_0 = '#skF_3'
    | m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_relat_1('#skF_5'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_170,c_428])).

tff(c_433,plain,
    ( k1_xboole_0 = '#skF_3'
    | m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_relat_1('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_430])).

tff(c_434,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_relat_1('#skF_5')))) ),
    inference(negUnitSimplification,[status(thm)],[c_409,c_433])).

tff(c_239,plain,(
    ! [D_106,A_4,B_108,B_5] :
      ( r2_hidden(k1_funct_1(D_106,A_4),B_108)
      | k1_xboole_0 = B_108
      | ~ m1_subset_1(D_106,k1_zfmisc_1(k2_zfmisc_1(B_5,B_108)))
      | ~ v1_funct_2(D_106,B_5,B_108)
      | ~ v1_funct_1(D_106)
      | v1_xboole_0(B_5)
      | ~ m1_subset_1(A_4,B_5) ) ),
    inference(resolution,[status(thm)],[c_12,c_236])).

tff(c_436,plain,(
    ! [A_4] :
      ( r2_hidden(k1_funct_1('#skF_4',A_4),k1_relat_1('#skF_5'))
      | k1_relat_1('#skF_5') = k1_xboole_0
      | ~ v1_funct_2('#skF_4','#skF_2',k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_4,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_434,c_239])).

tff(c_457,plain,(
    ! [A_4] :
      ( r2_hidden(k1_funct_1('#skF_4',A_4),k1_relat_1('#skF_5'))
      | k1_relat_1('#skF_5') = k1_xboole_0
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_4,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_278,c_436])).

tff(c_458,plain,(
    ! [A_4] :
      ( r2_hidden(k1_funct_1('#skF_4',A_4),k1_relat_1('#skF_5'))
      | k1_relat_1('#skF_5') = k1_xboole_0
      | ~ m1_subset_1(A_4,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_376,c_457])).

tff(c_483,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_458])).

tff(c_502,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_483,c_434])).

tff(c_508,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_502])).

tff(c_510,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_226,c_508])).

tff(c_513,plain,(
    ! [A_149] :
      ( r2_hidden(k1_funct_1('#skF_4',A_149),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(A_149,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_458])).

tff(c_28,plain,(
    ! [A_23,B_24,C_26] :
      ( k7_partfun1(A_23,B_24,C_26) = k1_funct_1(B_24,C_26)
      | ~ r2_hidden(C_26,k1_relat_1(B_24))
      | ~ v1_funct_1(B_24)
      | ~ v5_relat_1(B_24,A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_517,plain,(
    ! [A_23,A_149] :
      ( k7_partfun1(A_23,'#skF_5',k1_funct_1('#skF_4',A_149)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',A_149))
      | ~ v1_funct_1('#skF_5')
      | ~ v5_relat_1('#skF_5',A_23)
      | ~ v1_relat_1('#skF_5')
      | ~ m1_subset_1(A_149,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_513,c_28])).

tff(c_527,plain,(
    ! [A_153,A_154] :
      ( k7_partfun1(A_153,'#skF_5',k1_funct_1('#skF_4',A_154)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',A_154))
      | ~ v5_relat_1('#skF_5',A_153)
      | ~ m1_subset_1(A_154,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_56,c_517])).

tff(c_46,plain,(
    k7_partfun1('#skF_1','#skF_5',k1_funct_1('#skF_4','#skF_6')) != k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_533,plain,
    ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | ~ v5_relat_1('#skF_5','#skF_1')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_527,c_46])).

tff(c_539,plain,(
    k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_134,c_533])).

tff(c_622,plain,(
    ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_608,c_539])).

tff(c_634,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_622])).

tff(c_635,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_273])).

tff(c_655,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_635,c_2])).

tff(c_658,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_655])).

tff(c_659,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_225])).

tff(c_663,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_659,c_4])).

tff(c_667,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_663])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:51:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.24/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.50  
% 3.24/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.50  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.24/1.50  
% 3.24/1.50  %Foreground sorts:
% 3.24/1.50  
% 3.24/1.50  
% 3.24/1.50  %Background operators:
% 3.24/1.50  
% 3.24/1.50  
% 3.24/1.50  %Foreground operators:
% 3.24/1.50  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.24/1.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.24/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.24/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.24/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.24/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.24/1.50  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 3.24/1.50  tff('#skF_5', type, '#skF_5': $i).
% 3.24/1.50  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.24/1.50  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 3.24/1.50  tff('#skF_6', type, '#skF_6': $i).
% 3.24/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.24/1.50  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.24/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.24/1.50  tff('#skF_1', type, '#skF_1': $i).
% 3.24/1.50  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.24/1.50  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.24/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.24/1.50  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.24/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.24/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.24/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.24/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.24/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.24/1.50  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.24/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.24/1.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.24/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.24/1.50  
% 3.24/1.52  tff(f_172, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_funct_2)).
% 3.24/1.52  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.24/1.52  tff(f_116, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 3.24/1.52  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.24/1.52  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.24/1.52  tff(f_81, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 3.24/1.52  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.24/1.52  tff(f_36, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.24/1.52  tff(f_67, axiom, (![A, B]: ((~v1_xboole_0(A) & v1_xboole_0(B)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_partfun1)).
% 3.24/1.52  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.24/1.52  tff(f_128, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 3.24/1.52  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.24/1.52  tff(f_147, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(k2_relset_1(A, B, D), C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_2)).
% 3.24/1.52  tff(f_92, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 3.24/1.52  tff(c_48, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.24/1.52  tff(c_64, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.24/1.52  tff(c_52, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.24/1.52  tff(c_62, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.24/1.52  tff(c_60, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.24/1.52  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.24/1.52  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.24/1.52  tff(c_155, plain, (![A_86, B_87, C_88]: (k1_relset_1(A_86, B_87, C_88)=k1_relat_1(C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.24/1.52  tff(c_168, plain, (k1_relset_1('#skF_3', '#skF_1', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_155])).
% 3.24/1.52  tff(c_50, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_relset_1('#skF_3', '#skF_1', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.24/1.52  tff(c_170, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_168, c_50])).
% 3.24/1.52  tff(c_56, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.24/1.52  tff(c_580, plain, (![E_166, C_165, F_167, A_169, B_168, D_164]: (k1_funct_1(k8_funct_2(B_168, C_165, A_169, D_164, E_166), F_167)=k1_funct_1(E_166, k1_funct_1(D_164, F_167)) | k1_xboole_0=B_168 | ~r1_tarski(k2_relset_1(B_168, C_165, D_164), k1_relset_1(C_165, A_169, E_166)) | ~m1_subset_1(F_167, B_168) | ~m1_subset_1(E_166, k1_zfmisc_1(k2_zfmisc_1(C_165, A_169))) | ~v1_funct_1(E_166) | ~m1_subset_1(D_164, k1_zfmisc_1(k2_zfmisc_1(B_168, C_165))) | ~v1_funct_2(D_164, B_168, C_165) | ~v1_funct_1(D_164) | v1_xboole_0(C_165))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.24/1.52  tff(c_586, plain, (![B_168, D_164, F_167]: (k1_funct_1(k8_funct_2(B_168, '#skF_3', '#skF_1', D_164, '#skF_5'), F_167)=k1_funct_1('#skF_5', k1_funct_1(D_164, F_167)) | k1_xboole_0=B_168 | ~r1_tarski(k2_relset_1(B_168, '#skF_3', D_164), k1_relat_1('#skF_5')) | ~m1_subset_1(F_167, B_168) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_164, k1_zfmisc_1(k2_zfmisc_1(B_168, '#skF_3'))) | ~v1_funct_2(D_164, B_168, '#skF_3') | ~v1_funct_1(D_164) | v1_xboole_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_168, c_580])).
% 3.24/1.52  tff(c_594, plain, (![B_168, D_164, F_167]: (k1_funct_1(k8_funct_2(B_168, '#skF_3', '#skF_1', D_164, '#skF_5'), F_167)=k1_funct_1('#skF_5', k1_funct_1(D_164, F_167)) | k1_xboole_0=B_168 | ~r1_tarski(k2_relset_1(B_168, '#skF_3', D_164), k1_relat_1('#skF_5')) | ~m1_subset_1(F_167, B_168) | ~m1_subset_1(D_164, k1_zfmisc_1(k2_zfmisc_1(B_168, '#skF_3'))) | ~v1_funct_2(D_164, B_168, '#skF_3') | ~v1_funct_1(D_164) | v1_xboole_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_586])).
% 3.24/1.52  tff(c_601, plain, (![B_173, D_174, F_175]: (k1_funct_1(k8_funct_2(B_173, '#skF_3', '#skF_1', D_174, '#skF_5'), F_175)=k1_funct_1('#skF_5', k1_funct_1(D_174, F_175)) | k1_xboole_0=B_173 | ~r1_tarski(k2_relset_1(B_173, '#skF_3', D_174), k1_relat_1('#skF_5')) | ~m1_subset_1(F_175, B_173) | ~m1_subset_1(D_174, k1_zfmisc_1(k2_zfmisc_1(B_173, '#skF_3'))) | ~v1_funct_2(D_174, B_173, '#skF_3') | ~v1_funct_1(D_174))), inference(negUnitSimplification, [status(thm)], [c_64, c_594])).
% 3.24/1.52  tff(c_603, plain, (![F_175]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), F_175)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_175)) | k1_xboole_0='#skF_2' | ~m1_subset_1(F_175, '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_170, c_601])).
% 3.24/1.52  tff(c_606, plain, (![F_175]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), F_175)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_175)) | k1_xboole_0='#skF_2' | ~m1_subset_1(F_175, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_603])).
% 3.24/1.52  tff(c_608, plain, (![F_176]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), F_176)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_176)) | ~m1_subset_1(F_176, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_48, c_606])).
% 3.24/1.52  tff(c_121, plain, (![C_74, B_75, A_76]: (v5_relat_1(C_74, B_75) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_76, B_75))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.24/1.52  tff(c_134, plain, (v5_relat_1('#skF_5', '#skF_1')), inference(resolution, [status(thm)], [c_54, c_121])).
% 3.24/1.52  tff(c_95, plain, (![C_66, A_67, B_68]: (v1_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.24/1.52  tff(c_106, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_95])).
% 3.24/1.52  tff(c_201, plain, (![C_94, A_95, B_96]: (v1_partfun1(C_94, A_95) | ~v1_funct_2(C_94, A_95, B_96) | ~v1_funct_1(C_94) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))) | v1_xboole_0(B_96))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.24/1.52  tff(c_210, plain, (v1_partfun1('#skF_4', '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_58, c_201])).
% 3.24/1.52  tff(c_220, plain, (v1_partfun1('#skF_4', '#skF_2') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_210])).
% 3.24/1.52  tff(c_221, plain, (v1_partfun1('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_64, c_220])).
% 3.24/1.52  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.24/1.52  tff(c_8, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.24/1.52  tff(c_179, plain, (![C_89, A_90, B_91]: (~v1_partfun1(C_89, A_90) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))) | ~v1_xboole_0(B_91) | v1_xboole_0(A_90))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.24/1.52  tff(c_191, plain, (![C_89, A_2]: (~v1_partfun1(C_89, A_2) | ~m1_subset_1(C_89, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(A_2))), inference(superposition, [status(thm), theory('equality')], [c_8, c_179])).
% 3.24/1.52  tff(c_198, plain, (![C_89, A_2]: (~v1_partfun1(C_89, A_2) | ~m1_subset_1(C_89, k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(A_2))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_191])).
% 3.24/1.52  tff(c_225, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_221, c_198])).
% 3.24/1.52  tff(c_226, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_225])).
% 3.24/1.52  tff(c_12, plain, (![A_4, B_5]: (r2_hidden(A_4, B_5) | v1_xboole_0(B_5) | ~m1_subset_1(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.24/1.52  tff(c_236, plain, (![D_106, C_107, B_108, A_109]: (r2_hidden(k1_funct_1(D_106, C_107), B_108) | k1_xboole_0=B_108 | ~r2_hidden(C_107, A_109) | ~m1_subset_1(D_106, k1_zfmisc_1(k2_zfmisc_1(A_109, B_108))) | ~v1_funct_2(D_106, A_109, B_108) | ~v1_funct_1(D_106))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.24/1.52  tff(c_349, plain, (![D_127, A_128, B_129, B_130]: (r2_hidden(k1_funct_1(D_127, A_128), B_129) | k1_xboole_0=B_129 | ~m1_subset_1(D_127, k1_zfmisc_1(k2_zfmisc_1(B_130, B_129))) | ~v1_funct_2(D_127, B_130, B_129) | ~v1_funct_1(D_127) | v1_xboole_0(B_130) | ~m1_subset_1(A_128, B_130))), inference(resolution, [status(thm)], [c_12, c_236])).
% 3.24/1.52  tff(c_355, plain, (![A_128]: (r2_hidden(k1_funct_1('#skF_4', A_128), '#skF_3') | k1_xboole_0='#skF_3' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2') | ~m1_subset_1(A_128, '#skF_2'))), inference(resolution, [status(thm)], [c_58, c_349])).
% 3.24/1.52  tff(c_365, plain, (![A_128]: (r2_hidden(k1_funct_1('#skF_4', A_128), '#skF_3') | k1_xboole_0='#skF_3' | v1_xboole_0('#skF_2') | ~m1_subset_1(A_128, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_355])).
% 3.24/1.52  tff(c_367, plain, (v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_365])).
% 3.24/1.52  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.24/1.52  tff(c_370, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_367, c_4])).
% 3.24/1.52  tff(c_374, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_370])).
% 3.24/1.52  tff(c_376, plain, (~v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_365])).
% 3.24/1.52  tff(c_268, plain, (![B_116, D_117, A_118, C_119]: (k1_xboole_0=B_116 | v1_funct_2(D_117, A_118, C_119) | ~r1_tarski(k2_relset_1(A_118, B_116, D_117), C_119) | ~m1_subset_1(D_117, k1_zfmisc_1(k2_zfmisc_1(A_118, B_116))) | ~v1_funct_2(D_117, A_118, B_116) | ~v1_funct_1(D_117))), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.24/1.52  tff(c_270, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', '#skF_2', k1_relat_1('#skF_5')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_170, c_268])).
% 3.24/1.52  tff(c_273, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', '#skF_2', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_270])).
% 3.24/1.52  tff(c_278, plain, (v1_funct_2('#skF_4', '#skF_2', k1_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_273])).
% 3.24/1.52  tff(c_375, plain, (![A_128]: (k1_xboole_0='#skF_3' | r2_hidden(k1_funct_1('#skF_4', A_128), '#skF_3') | ~m1_subset_1(A_128, '#skF_2'))), inference(splitRight, [status(thm)], [c_365])).
% 3.24/1.52  tff(c_377, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_375])).
% 3.24/1.52  tff(c_404, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_377, c_2])).
% 3.24/1.52  tff(c_407, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_404])).
% 3.24/1.52  tff(c_409, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_375])).
% 3.24/1.52  tff(c_428, plain, (![B_139, D_140, A_141, C_142]: (k1_xboole_0=B_139 | m1_subset_1(D_140, k1_zfmisc_1(k2_zfmisc_1(A_141, C_142))) | ~r1_tarski(k2_relset_1(A_141, B_139, D_140), C_142) | ~m1_subset_1(D_140, k1_zfmisc_1(k2_zfmisc_1(A_141, B_139))) | ~v1_funct_2(D_140, A_141, B_139) | ~v1_funct_1(D_140))), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.24/1.52  tff(c_430, plain, (k1_xboole_0='#skF_3' | m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_relat_1('#skF_5')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_170, c_428])).
% 3.24/1.52  tff(c_433, plain, (k1_xboole_0='#skF_3' | m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_430])).
% 3.24/1.52  tff(c_434, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_relat_1('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_409, c_433])).
% 3.24/1.52  tff(c_239, plain, (![D_106, A_4, B_108, B_5]: (r2_hidden(k1_funct_1(D_106, A_4), B_108) | k1_xboole_0=B_108 | ~m1_subset_1(D_106, k1_zfmisc_1(k2_zfmisc_1(B_5, B_108))) | ~v1_funct_2(D_106, B_5, B_108) | ~v1_funct_1(D_106) | v1_xboole_0(B_5) | ~m1_subset_1(A_4, B_5))), inference(resolution, [status(thm)], [c_12, c_236])).
% 3.24/1.52  tff(c_436, plain, (![A_4]: (r2_hidden(k1_funct_1('#skF_4', A_4), k1_relat_1('#skF_5')) | k1_relat_1('#skF_5')=k1_xboole_0 | ~v1_funct_2('#skF_4', '#skF_2', k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2') | ~m1_subset_1(A_4, '#skF_2'))), inference(resolution, [status(thm)], [c_434, c_239])).
% 3.24/1.52  tff(c_457, plain, (![A_4]: (r2_hidden(k1_funct_1('#skF_4', A_4), k1_relat_1('#skF_5')) | k1_relat_1('#skF_5')=k1_xboole_0 | v1_xboole_0('#skF_2') | ~m1_subset_1(A_4, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_278, c_436])).
% 3.24/1.52  tff(c_458, plain, (![A_4]: (r2_hidden(k1_funct_1('#skF_4', A_4), k1_relat_1('#skF_5')) | k1_relat_1('#skF_5')=k1_xboole_0 | ~m1_subset_1(A_4, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_376, c_457])).
% 3.24/1.52  tff(c_483, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_458])).
% 3.24/1.52  tff(c_502, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_483, c_434])).
% 3.24/1.52  tff(c_508, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_502])).
% 3.24/1.52  tff(c_510, plain, $false, inference(negUnitSimplification, [status(thm)], [c_226, c_508])).
% 3.24/1.52  tff(c_513, plain, (![A_149]: (r2_hidden(k1_funct_1('#skF_4', A_149), k1_relat_1('#skF_5')) | ~m1_subset_1(A_149, '#skF_2'))), inference(splitRight, [status(thm)], [c_458])).
% 3.24/1.52  tff(c_28, plain, (![A_23, B_24, C_26]: (k7_partfun1(A_23, B_24, C_26)=k1_funct_1(B_24, C_26) | ~r2_hidden(C_26, k1_relat_1(B_24)) | ~v1_funct_1(B_24) | ~v5_relat_1(B_24, A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.24/1.52  tff(c_517, plain, (![A_23, A_149]: (k7_partfun1(A_23, '#skF_5', k1_funct_1('#skF_4', A_149))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', A_149)) | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', A_23) | ~v1_relat_1('#skF_5') | ~m1_subset_1(A_149, '#skF_2'))), inference(resolution, [status(thm)], [c_513, c_28])).
% 3.24/1.52  tff(c_527, plain, (![A_153, A_154]: (k7_partfun1(A_153, '#skF_5', k1_funct_1('#skF_4', A_154))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', A_154)) | ~v5_relat_1('#skF_5', A_153) | ~m1_subset_1(A_154, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_56, c_517])).
% 3.24/1.52  tff(c_46, plain, (k7_partfun1('#skF_1', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))!=k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.24/1.52  tff(c_533, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6')) | ~v5_relat_1('#skF_5', '#skF_1') | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_527, c_46])).
% 3.24/1.52  tff(c_539, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_134, c_533])).
% 3.24/1.52  tff(c_622, plain, (~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_608, c_539])).
% 3.24/1.52  tff(c_634, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_622])).
% 3.24/1.52  tff(c_635, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_273])).
% 3.24/1.52  tff(c_655, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_635, c_2])).
% 3.24/1.52  tff(c_658, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_655])).
% 3.24/1.52  tff(c_659, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_225])).
% 3.24/1.52  tff(c_663, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_659, c_4])).
% 3.24/1.52  tff(c_667, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_663])).
% 3.24/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.53  
% 3.24/1.53  Inference rules
% 3.24/1.53  ----------------------
% 3.24/1.53  #Ref     : 0
% 3.24/1.53  #Sup     : 108
% 3.24/1.53  #Fact    : 0
% 3.24/1.53  #Define  : 0
% 3.24/1.53  #Split   : 10
% 3.24/1.53  #Chain   : 0
% 3.24/1.53  #Close   : 0
% 3.24/1.53  
% 3.24/1.53  Ordering : KBO
% 3.24/1.53  
% 3.24/1.53  Simplification rules
% 3.24/1.53  ----------------------
% 3.24/1.53  #Subsume      : 7
% 3.24/1.53  #Demod        : 199
% 3.24/1.53  #Tautology    : 48
% 3.24/1.53  #SimpNegUnit  : 25
% 3.24/1.53  #BackRed      : 80
% 3.24/1.53  
% 3.24/1.53  #Partial instantiations: 0
% 3.24/1.53  #Strategies tried      : 1
% 3.24/1.53  
% 3.24/1.53  Timing (in seconds)
% 3.24/1.53  ----------------------
% 3.24/1.53  Preprocessing        : 0.36
% 3.24/1.53  Parsing              : 0.19
% 3.24/1.53  CNF conversion       : 0.03
% 3.24/1.53  Main loop            : 0.37
% 3.24/1.53  Inferencing          : 0.12
% 3.24/1.53  Reduction            : 0.13
% 3.24/1.53  Demodulation         : 0.09
% 3.24/1.53  BG Simplification    : 0.03
% 3.24/1.53  Subsumption          : 0.08
% 3.24/1.53  Abstraction          : 0.02
% 3.24/1.53  MUC search           : 0.00
% 3.24/1.53  Cooper               : 0.00
% 3.24/1.53  Total                : 0.77
% 3.24/1.53  Index Insertion      : 0.00
% 3.24/1.53  Index Deletion       : 0.00
% 3.24/1.53  Index Matching       : 0.00
% 3.24/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
