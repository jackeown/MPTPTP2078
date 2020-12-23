%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:45 EST 2020

% Result     : Theorem 4.56s
% Output     : CNFRefutation 4.56s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 454 expanded)
%              Number of leaves         :   46 ( 176 expanded)
%              Depth                    :   18
%              Number of atoms          :  328 (1804 expanded)
%              Number of equality atoms :   71 ( 336 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k7_partfun1,type,(
    k7_partfun1: ( $i * $i * $i ) > $i )).

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

tff(f_205,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_funct_2)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_161,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_149,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_2)).

tff(f_132,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_111,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_2)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_180,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & ~ v1_xboole_0(C)
              & v1_funct_2(C,A,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_funct_2)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_122,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_74,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_62,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_64,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_132,plain,(
    ! [C_76,A_77,B_78] :
      ( v1_relat_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_144,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_132])).

tff(c_66,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_68,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_178,plain,(
    ! [C_90,A_91,B_92] :
      ( v1_xboole_0(C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92)))
      | ~ v1_xboole_0(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_191,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_178])).

tff(c_195,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_191])).

tff(c_72,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_70,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_254,plain,(
    ! [D_112,C_113,B_114,A_115] :
      ( r2_hidden(k1_funct_1(D_112,C_113),B_114)
      | k1_xboole_0 = B_114
      | ~ r2_hidden(C_113,A_115)
      | ~ m1_subset_1(D_112,k1_zfmisc_1(k2_zfmisc_1(A_115,B_114)))
      | ~ v1_funct_2(D_112,A_115,B_114)
      | ~ v1_funct_1(D_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_553,plain,(
    ! [D_163,A_164,B_165,B_166] :
      ( r2_hidden(k1_funct_1(D_163,A_164),B_165)
      | k1_xboole_0 = B_165
      | ~ m1_subset_1(D_163,k1_zfmisc_1(k2_zfmisc_1(B_166,B_165)))
      | ~ v1_funct_2(D_163,B_166,B_165)
      | ~ v1_funct_1(D_163)
      | v1_xboole_0(B_166)
      | ~ m1_subset_1(A_164,B_166) ) ),
    inference(resolution,[status(thm)],[c_14,c_254])).

tff(c_555,plain,(
    ! [A_164] :
      ( r2_hidden(k1_funct_1('#skF_4',A_164),'#skF_3')
      | k1_xboole_0 = '#skF_3'
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_164,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_68,c_553])).

tff(c_564,plain,(
    ! [A_164] :
      ( r2_hidden(k1_funct_1('#skF_4',A_164),'#skF_3')
      | k1_xboole_0 = '#skF_3'
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_164,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_555])).

tff(c_565,plain,(
    ! [A_164] :
      ( r2_hidden(k1_funct_1('#skF_4',A_164),'#skF_3')
      | k1_xboole_0 = '#skF_3'
      | ~ m1_subset_1(A_164,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_195,c_564])).

tff(c_572,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_565])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_591,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_572,c_2])).

tff(c_594,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_591])).

tff(c_596,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_565])).

tff(c_805,plain,(
    ! [E_197,A_200,D_199,C_198,B_201] :
      ( k1_funct_1(k5_relat_1(D_199,E_197),C_198) = k1_funct_1(E_197,k1_funct_1(D_199,C_198))
      | k1_xboole_0 = B_201
      | ~ r2_hidden(C_198,A_200)
      | ~ v1_funct_1(E_197)
      | ~ v1_relat_1(E_197)
      | ~ m1_subset_1(D_199,k1_zfmisc_1(k2_zfmisc_1(A_200,B_201)))
      | ~ v1_funct_2(D_199,A_200,B_201)
      | ~ v1_funct_1(D_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_918,plain,(
    ! [D_242,E_241,B_238,B_239,A_240] :
      ( k1_funct_1(k5_relat_1(D_242,E_241),A_240) = k1_funct_1(E_241,k1_funct_1(D_242,A_240))
      | k1_xboole_0 = B_238
      | ~ v1_funct_1(E_241)
      | ~ v1_relat_1(E_241)
      | ~ m1_subset_1(D_242,k1_zfmisc_1(k2_zfmisc_1(B_239,B_238)))
      | ~ v1_funct_2(D_242,B_239,B_238)
      | ~ v1_funct_1(D_242)
      | v1_xboole_0(B_239)
      | ~ m1_subset_1(A_240,B_239) ) ),
    inference(resolution,[status(thm)],[c_14,c_805])).

tff(c_922,plain,(
    ! [E_241,A_240] :
      ( k1_funct_1(k5_relat_1('#skF_4',E_241),A_240) = k1_funct_1(E_241,k1_funct_1('#skF_4',A_240))
      | k1_xboole_0 = '#skF_3'
      | ~ v1_funct_1(E_241)
      | ~ v1_relat_1(E_241)
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_240,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_68,c_918])).

tff(c_935,plain,(
    ! [E_241,A_240] :
      ( k1_funct_1(k5_relat_1('#skF_4',E_241),A_240) = k1_funct_1(E_241,k1_funct_1('#skF_4',A_240))
      | k1_xboole_0 = '#skF_3'
      | ~ v1_funct_1(E_241)
      | ~ v1_relat_1(E_241)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_240,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_922])).

tff(c_948,plain,(
    ! [E_243,A_244] :
      ( k1_funct_1(k5_relat_1('#skF_4',E_243),A_244) = k1_funct_1(E_243,k1_funct_1('#skF_4',A_244))
      | ~ v1_funct_1(E_243)
      | ~ v1_relat_1(E_243)
      | ~ m1_subset_1(A_244,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_195,c_596,c_935])).

tff(c_615,plain,(
    ! [C_176,B_172,F_173,A_171,E_175,D_174] :
      ( k1_partfun1(A_171,B_172,C_176,D_174,E_175,F_173) = k5_relat_1(E_175,F_173)
      | ~ m1_subset_1(F_173,k1_zfmisc_1(k2_zfmisc_1(C_176,D_174)))
      | ~ v1_funct_1(F_173)
      | ~ m1_subset_1(E_175,k1_zfmisc_1(k2_zfmisc_1(A_171,B_172)))
      | ~ v1_funct_1(E_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_621,plain,(
    ! [A_171,B_172,E_175] :
      ( k1_partfun1(A_171,B_172,'#skF_3','#skF_1',E_175,'#skF_5') = k5_relat_1(E_175,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_175,k1_zfmisc_1(k2_zfmisc_1(A_171,B_172)))
      | ~ v1_funct_1(E_175) ) ),
    inference(resolution,[status(thm)],[c_64,c_615])).

tff(c_690,plain,(
    ! [A_181,B_182,E_183] :
      ( k1_partfun1(A_181,B_182,'#skF_3','#skF_1',E_183,'#skF_5') = k5_relat_1(E_183,'#skF_5')
      | ~ m1_subset_1(E_183,k1_zfmisc_1(k2_zfmisc_1(A_181,B_182)))
      | ~ v1_funct_1(E_183) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_621])).

tff(c_696,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_690])).

tff(c_711,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_696])).

tff(c_196,plain,(
    ! [A_93,B_94,C_95] :
      ( k1_relset_1(A_93,B_94,C_95) = k1_relat_1(C_95)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_210,plain,(
    k1_relset_1('#skF_3','#skF_1','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_196])).

tff(c_60,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_relset_1('#skF_3','#skF_1','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_212,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_60])).

tff(c_872,plain,(
    ! [D_215,A_217,B_216,C_213,E_214] :
      ( k1_partfun1(A_217,B_216,B_216,C_213,D_215,E_214) = k8_funct_2(A_217,B_216,C_213,D_215,E_214)
      | k1_xboole_0 = B_216
      | ~ r1_tarski(k2_relset_1(A_217,B_216,D_215),k1_relset_1(B_216,C_213,E_214))
      | ~ m1_subset_1(E_214,k1_zfmisc_1(k2_zfmisc_1(B_216,C_213)))
      | ~ v1_funct_1(E_214)
      | ~ m1_subset_1(D_215,k1_zfmisc_1(k2_zfmisc_1(A_217,B_216)))
      | ~ v1_funct_2(D_215,A_217,B_216)
      | ~ v1_funct_1(D_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_881,plain,(
    ! [A_217,D_215] :
      ( k1_partfun1(A_217,'#skF_3','#skF_3','#skF_1',D_215,'#skF_5') = k8_funct_2(A_217,'#skF_3','#skF_1',D_215,'#skF_5')
      | k1_xboole_0 = '#skF_3'
      | ~ r1_tarski(k2_relset_1(A_217,'#skF_3',D_215),k1_relat_1('#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_215,k1_zfmisc_1(k2_zfmisc_1(A_217,'#skF_3')))
      | ~ v1_funct_2(D_215,A_217,'#skF_3')
      | ~ v1_funct_1(D_215) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_872])).

tff(c_889,plain,(
    ! [A_217,D_215] :
      ( k1_partfun1(A_217,'#skF_3','#skF_3','#skF_1',D_215,'#skF_5') = k8_funct_2(A_217,'#skF_3','#skF_1',D_215,'#skF_5')
      | k1_xboole_0 = '#skF_3'
      | ~ r1_tarski(k2_relset_1(A_217,'#skF_3',D_215),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(D_215,k1_zfmisc_1(k2_zfmisc_1(A_217,'#skF_3')))
      | ~ v1_funct_2(D_215,A_217,'#skF_3')
      | ~ v1_funct_1(D_215) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_881])).

tff(c_905,plain,(
    ! [A_236,D_237] :
      ( k1_partfun1(A_236,'#skF_3','#skF_3','#skF_1',D_237,'#skF_5') = k8_funct_2(A_236,'#skF_3','#skF_1',D_237,'#skF_5')
      | ~ r1_tarski(k2_relset_1(A_236,'#skF_3',D_237),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(D_237,k1_zfmisc_1(k2_zfmisc_1(A_236,'#skF_3')))
      | ~ v1_funct_2(D_237,A_236,'#skF_3')
      | ~ v1_funct_1(D_237) ) ),
    inference(negUnitSimplification,[status(thm)],[c_596,c_889])).

tff(c_908,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_212,c_905])).

tff(c_911,plain,(
    k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_711,c_908])).

tff(c_147,plain,(
    ! [C_82,B_83,A_84] :
      ( v5_relat_1(C_82,B_83)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_84,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_161,plain,(
    v5_relat_1('#skF_5','#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_147])).

tff(c_8,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_546,plain,(
    ! [B_159,D_160,A_161,C_162] :
      ( k1_xboole_0 = B_159
      | v1_funct_2(D_160,A_161,C_162)
      | ~ r1_tarski(k2_relset_1(A_161,B_159,D_160),C_162)
      | ~ m1_subset_1(D_160,k1_zfmisc_1(k2_zfmisc_1(A_161,B_159)))
      | ~ v1_funct_2(D_160,A_161,B_159)
      | ~ v1_funct_1(D_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_548,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4','#skF_2',k1_relat_1('#skF_5'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_212,c_546])).

tff(c_551,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4','#skF_2',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_548])).

tff(c_552,plain,(
    v1_funct_2('#skF_4','#skF_2',k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_551])).

tff(c_630,plain,(
    ! [B_177,D_178,A_179,C_180] :
      ( k1_xboole_0 = B_177
      | m1_subset_1(D_178,k1_zfmisc_1(k2_zfmisc_1(A_179,C_180)))
      | ~ r1_tarski(k2_relset_1(A_179,B_177,D_178),C_180)
      | ~ m1_subset_1(D_178,k1_zfmisc_1(k2_zfmisc_1(A_179,B_177)))
      | ~ v1_funct_2(D_178,A_179,B_177)
      | ~ v1_funct_1(D_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_632,plain,
    ( k1_xboole_0 = '#skF_3'
    | m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_relat_1('#skF_5'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_212,c_630])).

tff(c_635,plain,
    ( k1_xboole_0 = '#skF_3'
    | m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_relat_1('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_632])).

tff(c_636,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_relat_1('#skF_5')))) ),
    inference(negUnitSimplification,[status(thm)],[c_596,c_635])).

tff(c_257,plain,(
    ! [D_112,A_7,B_114,B_8] :
      ( r2_hidden(k1_funct_1(D_112,A_7),B_114)
      | k1_xboole_0 = B_114
      | ~ m1_subset_1(D_112,k1_zfmisc_1(k2_zfmisc_1(B_8,B_114)))
      | ~ v1_funct_2(D_112,B_8,B_114)
      | ~ v1_funct_1(D_112)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(resolution,[status(thm)],[c_14,c_254])).

tff(c_640,plain,(
    ! [A_7] :
      ( r2_hidden(k1_funct_1('#skF_4',A_7),k1_relat_1('#skF_5'))
      | k1_relat_1('#skF_5') = k1_xboole_0
      | ~ v1_funct_2('#skF_4','#skF_2',k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_7,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_636,c_257])).

tff(c_667,plain,(
    ! [A_7] :
      ( r2_hidden(k1_funct_1('#skF_4',A_7),k1_relat_1('#skF_5'))
      | k1_relat_1('#skF_5') = k1_xboole_0
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_7,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_552,c_640])).

tff(c_668,plain,(
    ! [A_7] :
      ( r2_hidden(k1_funct_1('#skF_4',A_7),k1_relat_1('#skF_5'))
      | k1_relat_1('#skF_5') = k1_xboole_0
      | ~ m1_subset_1(A_7,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_195,c_667])).

tff(c_731,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_668])).

tff(c_222,plain,(
    ! [C_99,A_100,B_101] :
      ( ~ v1_xboole_0(C_99)
      | ~ v1_funct_2(C_99,A_100,B_101)
      | ~ v1_funct_1(C_99)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101)))
      | v1_xboole_0(B_101)
      | v1_xboole_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_225,plain,
    ( ~ v1_xboole_0('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_222])).

tff(c_237,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_225])).

tff(c_238,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_195,c_74,c_237])).

tff(c_12,plain,(
    ! [B_6,A_4] :
      ( v1_xboole_0(B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_4))
      | ~ v1_xboole_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_661,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_2',k1_relat_1('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_636,c_12])).

tff(c_684,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2',k1_relat_1('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_238,c_661])).

tff(c_744,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2',k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_731,c_684])).

tff(c_754,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_8,c_744])).

tff(c_757,plain,(
    ! [A_189] :
      ( r2_hidden(k1_funct_1('#skF_4',A_189),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(A_189,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_668])).

tff(c_36,plain,(
    ! [A_33,B_34,C_36] :
      ( k7_partfun1(A_33,B_34,C_36) = k1_funct_1(B_34,C_36)
      | ~ r2_hidden(C_36,k1_relat_1(B_34))
      | ~ v1_funct_1(B_34)
      | ~ v5_relat_1(B_34,A_33)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_761,plain,(
    ! [A_33,A_189] :
      ( k7_partfun1(A_33,'#skF_5',k1_funct_1('#skF_4',A_189)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',A_189))
      | ~ v1_funct_1('#skF_5')
      | ~ v5_relat_1('#skF_5',A_33)
      | ~ v1_relat_1('#skF_5')
      | ~ m1_subset_1(A_189,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_757,c_36])).

tff(c_820,plain,(
    ! [A_206,A_207] :
      ( k7_partfun1(A_206,'#skF_5',k1_funct_1('#skF_4',A_207)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',A_207))
      | ~ v5_relat_1('#skF_5',A_206)
      | ~ m1_subset_1(A_207,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_66,c_761])).

tff(c_56,plain,(
    k7_partfun1('#skF_1','#skF_5',k1_funct_1('#skF_4','#skF_6')) != k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_826,plain,
    ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | ~ v5_relat_1('#skF_5','#skF_1')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_820,c_56])).

tff(c_832,plain,(
    k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_161,c_826])).

tff(c_912,plain,(
    k1_funct_1(k5_relat_1('#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_911,c_832])).

tff(c_954,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_948,c_912])).

tff(c_966,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_144,c_66,c_954])).

tff(c_967,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_551])).

tff(c_986,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_967,c_2])).

tff(c_989,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_986])).

tff(c_991,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_191])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_1006,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_991,c_4])).

tff(c_1011,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1006])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:09:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.56/1.93  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.56/1.94  
% 4.56/1.94  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.56/1.94  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.56/1.94  
% 4.56/1.94  %Foreground sorts:
% 4.56/1.94  
% 4.56/1.94  
% 4.56/1.94  %Background operators:
% 4.56/1.94  
% 4.56/1.94  
% 4.56/1.94  %Foreground operators:
% 4.56/1.94  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.56/1.94  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.56/1.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.56/1.94  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.56/1.94  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.56/1.94  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.56/1.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.56/1.94  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 4.56/1.94  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.56/1.94  tff('#skF_5', type, '#skF_5': $i).
% 4.56/1.94  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.56/1.94  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 4.56/1.94  tff('#skF_6', type, '#skF_6': $i).
% 4.56/1.94  tff('#skF_2', type, '#skF_2': $i).
% 4.56/1.94  tff('#skF_3', type, '#skF_3': $i).
% 4.56/1.94  tff('#skF_1', type, '#skF_1': $i).
% 4.56/1.94  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.56/1.94  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.56/1.94  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.56/1.94  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.56/1.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.56/1.94  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.56/1.94  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.56/1.94  tff('#skF_4', type, '#skF_4': $i).
% 4.56/1.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.56/1.94  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.56/1.94  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.56/1.94  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.56/1.94  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.56/1.94  
% 4.56/1.97  tff(f_205, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t186_funct_2)).
% 4.56/1.97  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.56/1.97  tff(f_70, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 4.56/1.97  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 4.56/1.97  tff(f_161, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 4.56/1.97  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.56/1.97  tff(f_149, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_relat_1(E) & v1_funct_1(E)) => (r2_hidden(C, A) => ((B = k1_xboole_0) | (k1_funct_1(k5_relat_1(D, E), C) = k1_funct_1(E, k1_funct_1(D, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_funct_2)).
% 4.56/1.97  tff(f_132, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 4.56/1.97  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.56/1.97  tff(f_111, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (r1_tarski(k2_relset_1(A, B, D), k1_relset_1(B, C, E)) => ((B = k1_xboole_0) | (k8_funct_2(A, B, C, D, E) = k1_partfun1(A, B, B, C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_2)).
% 4.56/1.97  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.56/1.97  tff(f_36, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.56/1.97  tff(f_180, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(k2_relset_1(A, B, D), C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_2)).
% 4.56/1.97  tff(f_94, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => ((v1_funct_1(C) & ~v1_xboole_0(C)) & v1_funct_2(C, A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc6_funct_2)).
% 4.56/1.97  tff(f_43, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 4.56/1.97  tff(f_122, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_partfun1)).
% 4.56/1.97  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.56/1.97  tff(c_58, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_205])).
% 4.56/1.97  tff(c_74, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_205])).
% 4.56/1.97  tff(c_62, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_205])).
% 4.56/1.97  tff(c_64, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_205])).
% 4.56/1.97  tff(c_132, plain, (![C_76, A_77, B_78]: (v1_relat_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.56/1.97  tff(c_144, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_64, c_132])).
% 4.56/1.97  tff(c_66, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_205])).
% 4.56/1.97  tff(c_68, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_205])).
% 4.56/1.97  tff(c_178, plain, (![C_90, A_91, B_92]: (v1_xboole_0(C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))) | ~v1_xboole_0(A_91))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.56/1.97  tff(c_191, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_68, c_178])).
% 4.56/1.97  tff(c_195, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_191])).
% 4.56/1.97  tff(c_72, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_205])).
% 4.56/1.97  tff(c_70, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_205])).
% 4.56/1.97  tff(c_14, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.56/1.97  tff(c_254, plain, (![D_112, C_113, B_114, A_115]: (r2_hidden(k1_funct_1(D_112, C_113), B_114) | k1_xboole_0=B_114 | ~r2_hidden(C_113, A_115) | ~m1_subset_1(D_112, k1_zfmisc_1(k2_zfmisc_1(A_115, B_114))) | ~v1_funct_2(D_112, A_115, B_114) | ~v1_funct_1(D_112))), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.56/1.97  tff(c_553, plain, (![D_163, A_164, B_165, B_166]: (r2_hidden(k1_funct_1(D_163, A_164), B_165) | k1_xboole_0=B_165 | ~m1_subset_1(D_163, k1_zfmisc_1(k2_zfmisc_1(B_166, B_165))) | ~v1_funct_2(D_163, B_166, B_165) | ~v1_funct_1(D_163) | v1_xboole_0(B_166) | ~m1_subset_1(A_164, B_166))), inference(resolution, [status(thm)], [c_14, c_254])).
% 4.56/1.97  tff(c_555, plain, (![A_164]: (r2_hidden(k1_funct_1('#skF_4', A_164), '#skF_3') | k1_xboole_0='#skF_3' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2') | ~m1_subset_1(A_164, '#skF_2'))), inference(resolution, [status(thm)], [c_68, c_553])).
% 4.56/1.97  tff(c_564, plain, (![A_164]: (r2_hidden(k1_funct_1('#skF_4', A_164), '#skF_3') | k1_xboole_0='#skF_3' | v1_xboole_0('#skF_2') | ~m1_subset_1(A_164, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_555])).
% 4.56/1.97  tff(c_565, plain, (![A_164]: (r2_hidden(k1_funct_1('#skF_4', A_164), '#skF_3') | k1_xboole_0='#skF_3' | ~m1_subset_1(A_164, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_195, c_564])).
% 4.56/1.97  tff(c_572, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_565])).
% 4.56/1.97  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.56/1.97  tff(c_591, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_572, c_2])).
% 4.56/1.97  tff(c_594, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_591])).
% 4.56/1.97  tff(c_596, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_565])).
% 4.56/1.97  tff(c_805, plain, (![E_197, A_200, D_199, C_198, B_201]: (k1_funct_1(k5_relat_1(D_199, E_197), C_198)=k1_funct_1(E_197, k1_funct_1(D_199, C_198)) | k1_xboole_0=B_201 | ~r2_hidden(C_198, A_200) | ~v1_funct_1(E_197) | ~v1_relat_1(E_197) | ~m1_subset_1(D_199, k1_zfmisc_1(k2_zfmisc_1(A_200, B_201))) | ~v1_funct_2(D_199, A_200, B_201) | ~v1_funct_1(D_199))), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.56/1.97  tff(c_918, plain, (![D_242, E_241, B_238, B_239, A_240]: (k1_funct_1(k5_relat_1(D_242, E_241), A_240)=k1_funct_1(E_241, k1_funct_1(D_242, A_240)) | k1_xboole_0=B_238 | ~v1_funct_1(E_241) | ~v1_relat_1(E_241) | ~m1_subset_1(D_242, k1_zfmisc_1(k2_zfmisc_1(B_239, B_238))) | ~v1_funct_2(D_242, B_239, B_238) | ~v1_funct_1(D_242) | v1_xboole_0(B_239) | ~m1_subset_1(A_240, B_239))), inference(resolution, [status(thm)], [c_14, c_805])).
% 4.56/1.97  tff(c_922, plain, (![E_241, A_240]: (k1_funct_1(k5_relat_1('#skF_4', E_241), A_240)=k1_funct_1(E_241, k1_funct_1('#skF_4', A_240)) | k1_xboole_0='#skF_3' | ~v1_funct_1(E_241) | ~v1_relat_1(E_241) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2') | ~m1_subset_1(A_240, '#skF_2'))), inference(resolution, [status(thm)], [c_68, c_918])).
% 4.56/1.97  tff(c_935, plain, (![E_241, A_240]: (k1_funct_1(k5_relat_1('#skF_4', E_241), A_240)=k1_funct_1(E_241, k1_funct_1('#skF_4', A_240)) | k1_xboole_0='#skF_3' | ~v1_funct_1(E_241) | ~v1_relat_1(E_241) | v1_xboole_0('#skF_2') | ~m1_subset_1(A_240, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_922])).
% 4.56/1.97  tff(c_948, plain, (![E_243, A_244]: (k1_funct_1(k5_relat_1('#skF_4', E_243), A_244)=k1_funct_1(E_243, k1_funct_1('#skF_4', A_244)) | ~v1_funct_1(E_243) | ~v1_relat_1(E_243) | ~m1_subset_1(A_244, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_195, c_596, c_935])).
% 4.56/1.97  tff(c_615, plain, (![C_176, B_172, F_173, A_171, E_175, D_174]: (k1_partfun1(A_171, B_172, C_176, D_174, E_175, F_173)=k5_relat_1(E_175, F_173) | ~m1_subset_1(F_173, k1_zfmisc_1(k2_zfmisc_1(C_176, D_174))) | ~v1_funct_1(F_173) | ~m1_subset_1(E_175, k1_zfmisc_1(k2_zfmisc_1(A_171, B_172))) | ~v1_funct_1(E_175))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.56/1.97  tff(c_621, plain, (![A_171, B_172, E_175]: (k1_partfun1(A_171, B_172, '#skF_3', '#skF_1', E_175, '#skF_5')=k5_relat_1(E_175, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_175, k1_zfmisc_1(k2_zfmisc_1(A_171, B_172))) | ~v1_funct_1(E_175))), inference(resolution, [status(thm)], [c_64, c_615])).
% 4.56/1.97  tff(c_690, plain, (![A_181, B_182, E_183]: (k1_partfun1(A_181, B_182, '#skF_3', '#skF_1', E_183, '#skF_5')=k5_relat_1(E_183, '#skF_5') | ~m1_subset_1(E_183, k1_zfmisc_1(k2_zfmisc_1(A_181, B_182))) | ~v1_funct_1(E_183))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_621])).
% 4.56/1.97  tff(c_696, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_690])).
% 4.56/1.97  tff(c_711, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_696])).
% 4.56/1.97  tff(c_196, plain, (![A_93, B_94, C_95]: (k1_relset_1(A_93, B_94, C_95)=k1_relat_1(C_95) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.56/1.97  tff(c_210, plain, (k1_relset_1('#skF_3', '#skF_1', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_64, c_196])).
% 4.56/1.97  tff(c_60, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_relset_1('#skF_3', '#skF_1', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_205])).
% 4.56/1.97  tff(c_212, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_210, c_60])).
% 4.56/1.97  tff(c_872, plain, (![D_215, A_217, B_216, C_213, E_214]: (k1_partfun1(A_217, B_216, B_216, C_213, D_215, E_214)=k8_funct_2(A_217, B_216, C_213, D_215, E_214) | k1_xboole_0=B_216 | ~r1_tarski(k2_relset_1(A_217, B_216, D_215), k1_relset_1(B_216, C_213, E_214)) | ~m1_subset_1(E_214, k1_zfmisc_1(k2_zfmisc_1(B_216, C_213))) | ~v1_funct_1(E_214) | ~m1_subset_1(D_215, k1_zfmisc_1(k2_zfmisc_1(A_217, B_216))) | ~v1_funct_2(D_215, A_217, B_216) | ~v1_funct_1(D_215))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.56/1.97  tff(c_881, plain, (![A_217, D_215]: (k1_partfun1(A_217, '#skF_3', '#skF_3', '#skF_1', D_215, '#skF_5')=k8_funct_2(A_217, '#skF_3', '#skF_1', D_215, '#skF_5') | k1_xboole_0='#skF_3' | ~r1_tarski(k2_relset_1(A_217, '#skF_3', D_215), k1_relat_1('#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_215, k1_zfmisc_1(k2_zfmisc_1(A_217, '#skF_3'))) | ~v1_funct_2(D_215, A_217, '#skF_3') | ~v1_funct_1(D_215))), inference(superposition, [status(thm), theory('equality')], [c_210, c_872])).
% 4.56/1.97  tff(c_889, plain, (![A_217, D_215]: (k1_partfun1(A_217, '#skF_3', '#skF_3', '#skF_1', D_215, '#skF_5')=k8_funct_2(A_217, '#skF_3', '#skF_1', D_215, '#skF_5') | k1_xboole_0='#skF_3' | ~r1_tarski(k2_relset_1(A_217, '#skF_3', D_215), k1_relat_1('#skF_5')) | ~m1_subset_1(D_215, k1_zfmisc_1(k2_zfmisc_1(A_217, '#skF_3'))) | ~v1_funct_2(D_215, A_217, '#skF_3') | ~v1_funct_1(D_215))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_881])).
% 4.56/1.97  tff(c_905, plain, (![A_236, D_237]: (k1_partfun1(A_236, '#skF_3', '#skF_3', '#skF_1', D_237, '#skF_5')=k8_funct_2(A_236, '#skF_3', '#skF_1', D_237, '#skF_5') | ~r1_tarski(k2_relset_1(A_236, '#skF_3', D_237), k1_relat_1('#skF_5')) | ~m1_subset_1(D_237, k1_zfmisc_1(k2_zfmisc_1(A_236, '#skF_3'))) | ~v1_funct_2(D_237, A_236, '#skF_3') | ~v1_funct_1(D_237))), inference(negUnitSimplification, [status(thm)], [c_596, c_889])).
% 4.56/1.97  tff(c_908, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_212, c_905])).
% 4.56/1.97  tff(c_911, plain, (k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_711, c_908])).
% 4.56/1.97  tff(c_147, plain, (![C_82, B_83, A_84]: (v5_relat_1(C_82, B_83) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_84, B_83))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.56/1.97  tff(c_161, plain, (v5_relat_1('#skF_5', '#skF_1')), inference(resolution, [status(thm)], [c_64, c_147])).
% 4.56/1.97  tff(c_8, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.56/1.97  tff(c_546, plain, (![B_159, D_160, A_161, C_162]: (k1_xboole_0=B_159 | v1_funct_2(D_160, A_161, C_162) | ~r1_tarski(k2_relset_1(A_161, B_159, D_160), C_162) | ~m1_subset_1(D_160, k1_zfmisc_1(k2_zfmisc_1(A_161, B_159))) | ~v1_funct_2(D_160, A_161, B_159) | ~v1_funct_1(D_160))), inference(cnfTransformation, [status(thm)], [f_180])).
% 4.56/1.97  tff(c_548, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', '#skF_2', k1_relat_1('#skF_5')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_212, c_546])).
% 4.56/1.97  tff(c_551, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', '#skF_2', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_548])).
% 4.56/1.97  tff(c_552, plain, (v1_funct_2('#skF_4', '#skF_2', k1_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_551])).
% 4.56/1.97  tff(c_630, plain, (![B_177, D_178, A_179, C_180]: (k1_xboole_0=B_177 | m1_subset_1(D_178, k1_zfmisc_1(k2_zfmisc_1(A_179, C_180))) | ~r1_tarski(k2_relset_1(A_179, B_177, D_178), C_180) | ~m1_subset_1(D_178, k1_zfmisc_1(k2_zfmisc_1(A_179, B_177))) | ~v1_funct_2(D_178, A_179, B_177) | ~v1_funct_1(D_178))), inference(cnfTransformation, [status(thm)], [f_180])).
% 4.56/1.97  tff(c_632, plain, (k1_xboole_0='#skF_3' | m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_relat_1('#skF_5')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_212, c_630])).
% 4.56/1.97  tff(c_635, plain, (k1_xboole_0='#skF_3' | m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_632])).
% 4.56/1.97  tff(c_636, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_relat_1('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_596, c_635])).
% 4.56/1.97  tff(c_257, plain, (![D_112, A_7, B_114, B_8]: (r2_hidden(k1_funct_1(D_112, A_7), B_114) | k1_xboole_0=B_114 | ~m1_subset_1(D_112, k1_zfmisc_1(k2_zfmisc_1(B_8, B_114))) | ~v1_funct_2(D_112, B_8, B_114) | ~v1_funct_1(D_112) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(resolution, [status(thm)], [c_14, c_254])).
% 4.56/1.97  tff(c_640, plain, (![A_7]: (r2_hidden(k1_funct_1('#skF_4', A_7), k1_relat_1('#skF_5')) | k1_relat_1('#skF_5')=k1_xboole_0 | ~v1_funct_2('#skF_4', '#skF_2', k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2') | ~m1_subset_1(A_7, '#skF_2'))), inference(resolution, [status(thm)], [c_636, c_257])).
% 4.56/1.97  tff(c_667, plain, (![A_7]: (r2_hidden(k1_funct_1('#skF_4', A_7), k1_relat_1('#skF_5')) | k1_relat_1('#skF_5')=k1_xboole_0 | v1_xboole_0('#skF_2') | ~m1_subset_1(A_7, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_552, c_640])).
% 4.56/1.97  tff(c_668, plain, (![A_7]: (r2_hidden(k1_funct_1('#skF_4', A_7), k1_relat_1('#skF_5')) | k1_relat_1('#skF_5')=k1_xboole_0 | ~m1_subset_1(A_7, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_195, c_667])).
% 4.56/1.97  tff(c_731, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_668])).
% 4.56/1.97  tff(c_222, plain, (![C_99, A_100, B_101]: (~v1_xboole_0(C_99) | ~v1_funct_2(C_99, A_100, B_101) | ~v1_funct_1(C_99) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))) | v1_xboole_0(B_101) | v1_xboole_0(A_100))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.56/1.97  tff(c_225, plain, (~v1_xboole_0('#skF_4') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_68, c_222])).
% 4.56/1.97  tff(c_237, plain, (~v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_225])).
% 4.56/1.97  tff(c_238, plain, (~v1_xboole_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_195, c_74, c_237])).
% 4.56/1.97  tff(c_12, plain, (![B_6, A_4]: (v1_xboole_0(B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_4)) | ~v1_xboole_0(A_4))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.56/1.97  tff(c_661, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(k2_zfmisc_1('#skF_2', k1_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_636, c_12])).
% 4.56/1.97  tff(c_684, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', k1_relat_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_238, c_661])).
% 4.56/1.97  tff(c_744, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_731, c_684])).
% 4.56/1.97  tff(c_754, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_8, c_744])).
% 4.56/1.97  tff(c_757, plain, (![A_189]: (r2_hidden(k1_funct_1('#skF_4', A_189), k1_relat_1('#skF_5')) | ~m1_subset_1(A_189, '#skF_2'))), inference(splitRight, [status(thm)], [c_668])).
% 4.56/1.97  tff(c_36, plain, (![A_33, B_34, C_36]: (k7_partfun1(A_33, B_34, C_36)=k1_funct_1(B_34, C_36) | ~r2_hidden(C_36, k1_relat_1(B_34)) | ~v1_funct_1(B_34) | ~v5_relat_1(B_34, A_33) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.56/1.97  tff(c_761, plain, (![A_33, A_189]: (k7_partfun1(A_33, '#skF_5', k1_funct_1('#skF_4', A_189))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', A_189)) | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', A_33) | ~v1_relat_1('#skF_5') | ~m1_subset_1(A_189, '#skF_2'))), inference(resolution, [status(thm)], [c_757, c_36])).
% 4.56/1.97  tff(c_820, plain, (![A_206, A_207]: (k7_partfun1(A_206, '#skF_5', k1_funct_1('#skF_4', A_207))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', A_207)) | ~v5_relat_1('#skF_5', A_206) | ~m1_subset_1(A_207, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_66, c_761])).
% 4.56/1.97  tff(c_56, plain, (k7_partfun1('#skF_1', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))!=k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_205])).
% 4.56/1.97  tff(c_826, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6')) | ~v5_relat_1('#skF_5', '#skF_1') | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_820, c_56])).
% 4.56/1.97  tff(c_832, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_161, c_826])).
% 4.56/1.97  tff(c_912, plain, (k1_funct_1(k5_relat_1('#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_911, c_832])).
% 4.56/1.97  tff(c_954, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_948, c_912])).
% 4.56/1.97  tff(c_966, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_144, c_66, c_954])).
% 4.56/1.97  tff(c_967, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_551])).
% 4.56/1.97  tff(c_986, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_967, c_2])).
% 4.56/1.97  tff(c_989, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_986])).
% 4.56/1.97  tff(c_991, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_191])).
% 4.56/1.97  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 4.56/1.97  tff(c_1006, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_991, c_4])).
% 4.56/1.97  tff(c_1011, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_1006])).
% 4.56/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.56/1.97  
% 4.56/1.97  Inference rules
% 4.56/1.97  ----------------------
% 4.56/1.97  #Ref     : 0
% 4.56/1.97  #Sup     : 196
% 4.56/1.97  #Fact    : 0
% 4.56/1.97  #Define  : 0
% 4.56/1.97  #Split   : 12
% 4.56/1.97  #Chain   : 0
% 4.56/1.97  #Close   : 0
% 4.56/1.97  
% 4.56/1.97  Ordering : KBO
% 4.56/1.97  
% 4.56/1.97  Simplification rules
% 4.56/1.97  ----------------------
% 4.56/1.97  #Subsume      : 11
% 4.56/1.97  #Demod        : 228
% 4.56/1.97  #Tautology    : 85
% 4.56/1.97  #SimpNegUnit  : 23
% 4.56/1.97  #BackRed      : 87
% 4.56/1.97  
% 4.56/1.97  #Partial instantiations: 0
% 4.56/1.97  #Strategies tried      : 1
% 4.56/1.97  
% 4.56/1.97  Timing (in seconds)
% 4.56/1.97  ----------------------
% 4.56/1.97  Preprocessing        : 0.53
% 4.56/1.97  Parsing              : 0.28
% 4.56/1.97  CNF conversion       : 0.04
% 4.56/1.97  Main loop            : 0.58
% 4.56/1.97  Inferencing          : 0.18
% 4.56/1.97  Reduction            : 0.21
% 4.56/1.97  Demodulation         : 0.15
% 4.56/1.97  BG Simplification    : 0.04
% 4.56/1.97  Subsumption          : 0.12
% 4.56/1.97  Abstraction          : 0.03
% 4.56/1.97  MUC search           : 0.00
% 4.56/1.97  Cooper               : 0.00
% 4.56/1.97  Total                : 1.17
% 4.56/1.97  Index Insertion      : 0.00
% 4.56/1.97  Index Deletion       : 0.00
% 4.56/1.97  Index Matching       : 0.00
% 4.56/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
