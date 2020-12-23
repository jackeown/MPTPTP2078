%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:06 EST 2020

% Result     : Theorem 4.16s
% Output     : CNFRefutation 4.51s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 604 expanded)
%              Number of leaves         :   38 ( 227 expanded)
%              Depth                    :   19
%              Number of atoms          :  175 (1983 expanded)
%              Number of equality atoms :   33 ( 388 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_177,negated_conjecture,(
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

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_115,axiom,(
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

tff(f_155,axiom,(
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

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_128,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_74,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_126,plain,(
    ! [C_62,A_63,B_64] :
      ( v1_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_134,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_126])).

tff(c_16,plain,(
    ! [B_8,A_7] :
      ( r1_tarski(k2_relat_1(B_8),A_7)
      | ~ v5_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_211,plain,(
    ! [A_96,B_97,C_98] :
      ( k2_relset_1(A_96,B_97,C_98) = k2_relat_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_225,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_211])).

tff(c_70,plain,(
    ~ r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_226,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_70])).

tff(c_233,plain,
    ( ~ v5_relat_1('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_226])).

tff(c_236,plain,(
    ~ v5_relat_1('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_233])).

tff(c_78,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_76,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_175,plain,(
    ! [A_86,B_87,C_88] :
      ( k1_relset_1(A_86,B_87,C_88) = k1_relat_1(C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_185,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_175])).

tff(c_320,plain,(
    ! [B_125,A_126,C_127] :
      ( k1_xboole_0 = B_125
      | k1_relset_1(A_126,B_125,C_127) = A_126
      | ~ v1_funct_2(C_127,A_126,B_125)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_126,B_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_329,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_320])).

tff(c_340,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_185,c_329])).

tff(c_342,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_340])).

tff(c_625,plain,(
    ! [C_164,B_165] :
      ( r2_hidden('#skF_1'(k1_relat_1(C_164),B_165,C_164),k1_relat_1(C_164))
      | m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_164),B_165)))
      | ~ v1_funct_1(C_164)
      | ~ v1_relat_1(C_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_634,plain,(
    ! [B_165] :
      ( r2_hidden('#skF_1'(k1_relat_1('#skF_5'),B_165,'#skF_5'),'#skF_3')
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),B_165)))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_625])).

tff(c_645,plain,(
    ! [B_166] :
      ( r2_hidden('#skF_1'('#skF_3',B_166,'#skF_5'),'#skF_3')
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_166))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_78,c_342,c_342,c_634])).

tff(c_20,plain,(
    ! [C_14,B_13,A_12] :
      ( v5_relat_1(C_14,B_13)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_693,plain,(
    ! [B_167] :
      ( v5_relat_1('#skF_5',B_167)
      | r2_hidden('#skF_1'('#skF_3',B_167,'#skF_5'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_645,c_20])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,B_4)
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_697,plain,(
    ! [B_167] :
      ( m1_subset_1('#skF_1'('#skF_3',B_167,'#skF_5'),'#skF_3')
      | v5_relat_1('#skF_5',B_167) ) ),
    inference(resolution,[status(thm)],[c_693,c_8])).

tff(c_82,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_859,plain,(
    ! [A_177,B_178,C_179,D_180] :
      ( k3_funct_2(A_177,B_178,C_179,D_180) = k1_funct_1(C_179,D_180)
      | ~ m1_subset_1(D_180,A_177)
      | ~ m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1(A_177,B_178)))
      | ~ v1_funct_2(C_179,A_177,B_178)
      | ~ v1_funct_1(C_179)
      | v1_xboole_0(A_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_865,plain,(
    ! [B_178,C_179,B_167] :
      ( k3_funct_2('#skF_3',B_178,C_179,'#skF_1'('#skF_3',B_167,'#skF_5')) = k1_funct_1(C_179,'#skF_1'('#skF_3',B_167,'#skF_5'))
      | ~ m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_178)))
      | ~ v1_funct_2(C_179,'#skF_3',B_178)
      | ~ v1_funct_1(C_179)
      | v1_xboole_0('#skF_3')
      | v5_relat_1('#skF_5',B_167) ) ),
    inference(resolution,[status(thm)],[c_697,c_859])).

tff(c_973,plain,(
    ! [B_194,C_195,B_196] :
      ( k3_funct_2('#skF_3',B_194,C_195,'#skF_1'('#skF_3',B_196,'#skF_5')) = k1_funct_1(C_195,'#skF_1'('#skF_3',B_196,'#skF_5'))
      | ~ m1_subset_1(C_195,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_194)))
      | ~ v1_funct_2(C_195,'#skF_3',B_194)
      | ~ v1_funct_1(C_195)
      | v5_relat_1('#skF_5',B_196) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_865])).

tff(c_982,plain,(
    ! [B_196] :
      ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'('#skF_3',B_196,'#skF_5')) = k1_funct_1('#skF_5','#skF_1'('#skF_3',B_196,'#skF_5'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5')
      | v5_relat_1('#skF_5',B_196) ) ),
    inference(resolution,[status(thm)],[c_74,c_973])).

tff(c_1628,plain,(
    ! [B_269] :
      ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'('#skF_3',B_269,'#skF_5')) = k1_funct_1('#skF_5','#skF_1'('#skF_3',B_269,'#skF_5'))
      | v5_relat_1('#skF_5',B_269) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_982])).

tff(c_72,plain,(
    ! [E_54] :
      ( r2_hidden(k3_funct_2('#skF_3','#skF_4','#skF_5',E_54),'#skF_2')
      | ~ m1_subset_1(E_54,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_1661,plain,(
    ! [B_274] :
      ( r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_274,'#skF_5')),'#skF_2')
      | ~ m1_subset_1('#skF_1'('#skF_3',B_274,'#skF_5'),'#skF_3')
      | v5_relat_1('#skF_5',B_274) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1628,c_72])).

tff(c_594,plain,(
    ! [C_157,B_158] :
      ( ~ r2_hidden(k1_funct_1(C_157,'#skF_1'(k1_relat_1(C_157),B_158,C_157)),B_158)
      | v1_funct_2(C_157,k1_relat_1(C_157),B_158)
      | ~ v1_funct_1(C_157)
      | ~ v1_relat_1(C_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_597,plain,(
    ! [B_158] :
      ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_158,'#skF_5')),B_158)
      | v1_funct_2('#skF_5',k1_relat_1('#skF_5'),B_158)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_594])).

tff(c_599,plain,(
    ! [B_158] :
      ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_158,'#skF_5')),B_158)
      | v1_funct_2('#skF_5','#skF_3',B_158) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_78,c_342,c_597])).

tff(c_1669,plain,
    ( v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3')
    | v5_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_1661,c_599])).

tff(c_1678,plain,
    ( v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_236,c_1669])).

tff(c_1680,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1678])).

tff(c_1720,plain,(
    v5_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_697,c_1680])).

tff(c_1729,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_236,c_1720])).

tff(c_1731,plain,(
    m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_1678])).

tff(c_749,plain,(
    ! [C_169,B_170] :
      ( ~ r2_hidden(k1_funct_1(C_169,'#skF_1'(k1_relat_1(C_169),B_170,C_169)),B_170)
      | m1_subset_1(C_169,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_169),B_170)))
      | ~ v1_funct_1(C_169)
      | ~ v1_relat_1(C_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_752,plain,(
    ! [B_170] :
      ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_170,'#skF_5')),B_170)
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),B_170)))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_749])).

tff(c_754,plain,(
    ! [B_170] :
      ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_170,'#skF_5')),B_170)
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_170))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_78,c_342,c_752])).

tff(c_1665,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3')
    | v5_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_1661,c_754])).

tff(c_1675,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_236,c_1665])).

tff(c_1738,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1731,c_1675])).

tff(c_1772,plain,(
    v5_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_1738,c_20])).

tff(c_1812,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_236,c_1772])).

tff(c_1813,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_340])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1832,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1813,c_1813,c_4])).

tff(c_1843,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1832,c_74])).

tff(c_6,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_161,plain,(
    ! [C_80,B_81,A_82] :
      ( v5_relat_1(C_80,B_81)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_82,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_170,plain,(
    ! [C_80,B_2] :
      ( v5_relat_1(C_80,B_2)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_161])).

tff(c_1912,plain,(
    ! [C_281,B_282] :
      ( v5_relat_1(C_281,B_282)
      | ~ m1_subset_1(C_281,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1813,c_170])).

tff(c_1915,plain,(
    ! [B_282] : v5_relat_1('#skF_5',B_282) ),
    inference(resolution,[status(thm)],[c_1843,c_1912])).

tff(c_1935,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1915,c_236])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:08:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.16/1.76  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.16/1.76  
% 4.16/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.16/1.77  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 4.16/1.77  
% 4.16/1.77  %Foreground sorts:
% 4.16/1.77  
% 4.16/1.77  
% 4.16/1.77  %Background operators:
% 4.16/1.77  
% 4.16/1.77  
% 4.16/1.77  %Foreground operators:
% 4.16/1.77  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.16/1.77  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.16/1.77  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.16/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.16/1.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.16/1.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.16/1.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.16/1.77  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.16/1.77  tff('#skF_5', type, '#skF_5': $i).
% 4.16/1.77  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.16/1.77  tff('#skF_2', type, '#skF_2': $i).
% 4.16/1.77  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.16/1.77  tff('#skF_3', type, '#skF_3': $i).
% 4.16/1.77  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.16/1.77  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.16/1.77  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.16/1.77  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.16/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.16/1.77  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.16/1.77  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.16/1.77  tff('#skF_4', type, '#skF_4': $i).
% 4.16/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.16/1.77  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.16/1.77  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.16/1.77  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 4.16/1.77  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.16/1.77  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.16/1.77  
% 4.51/1.78  tff(f_177, negated_conjecture, ~(![A, B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((![E]: (m1_subset_1(E, B) => r2_hidden(k3_funct_2(B, C, D, E), A))) => r1_tarski(k2_relset_1(B, C, D), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t191_funct_2)).
% 4.51/1.78  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.51/1.78  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 4.51/1.78  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.51/1.78  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.51/1.78  tff(f_115, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.51/1.78  tff(f_155, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(C) = A) & (![D]: (r2_hidden(D, A) => r2_hidden(k1_funct_1(C, D), B)))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_funct_2)).
% 4.51/1.78  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.51/1.78  tff(f_35, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 4.51/1.78  tff(f_128, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 4.51/1.78  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.51/1.78  tff(c_74, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_177])).
% 4.51/1.78  tff(c_126, plain, (![C_62, A_63, B_64]: (v1_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.51/1.78  tff(c_134, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_126])).
% 4.51/1.78  tff(c_16, plain, (![B_8, A_7]: (r1_tarski(k2_relat_1(B_8), A_7) | ~v5_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.51/1.78  tff(c_211, plain, (![A_96, B_97, C_98]: (k2_relset_1(A_96, B_97, C_98)=k2_relat_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.51/1.78  tff(c_225, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_211])).
% 4.51/1.78  tff(c_70, plain, (~r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_177])).
% 4.51/1.78  tff(c_226, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_225, c_70])).
% 4.51/1.78  tff(c_233, plain, (~v5_relat_1('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_16, c_226])).
% 4.51/1.78  tff(c_236, plain, (~v5_relat_1('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_134, c_233])).
% 4.51/1.78  tff(c_78, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_177])).
% 4.51/1.78  tff(c_76, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_177])).
% 4.51/1.78  tff(c_175, plain, (![A_86, B_87, C_88]: (k1_relset_1(A_86, B_87, C_88)=k1_relat_1(C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.51/1.78  tff(c_185, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_175])).
% 4.51/1.78  tff(c_320, plain, (![B_125, A_126, C_127]: (k1_xboole_0=B_125 | k1_relset_1(A_126, B_125, C_127)=A_126 | ~v1_funct_2(C_127, A_126, B_125) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_126, B_125))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.51/1.78  tff(c_329, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_74, c_320])).
% 4.51/1.78  tff(c_340, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_185, c_329])).
% 4.51/1.78  tff(c_342, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_340])).
% 4.51/1.78  tff(c_625, plain, (![C_164, B_165]: (r2_hidden('#skF_1'(k1_relat_1(C_164), B_165, C_164), k1_relat_1(C_164)) | m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_164), B_165))) | ~v1_funct_1(C_164) | ~v1_relat_1(C_164))), inference(cnfTransformation, [status(thm)], [f_155])).
% 4.51/1.78  tff(c_634, plain, (![B_165]: (r2_hidden('#skF_1'(k1_relat_1('#skF_5'), B_165, '#skF_5'), '#skF_3') | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), B_165))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_342, c_625])).
% 4.51/1.78  tff(c_645, plain, (![B_166]: (r2_hidden('#skF_1'('#skF_3', B_166, '#skF_5'), '#skF_3') | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_166))))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_78, c_342, c_342, c_634])).
% 4.51/1.78  tff(c_20, plain, (![C_14, B_13, A_12]: (v5_relat_1(C_14, B_13) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.51/1.78  tff(c_693, plain, (![B_167]: (v5_relat_1('#skF_5', B_167) | r2_hidden('#skF_1'('#skF_3', B_167, '#skF_5'), '#skF_3'))), inference(resolution, [status(thm)], [c_645, c_20])).
% 4.51/1.78  tff(c_8, plain, (![A_3, B_4]: (m1_subset_1(A_3, B_4) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.51/1.78  tff(c_697, plain, (![B_167]: (m1_subset_1('#skF_1'('#skF_3', B_167, '#skF_5'), '#skF_3') | v5_relat_1('#skF_5', B_167))), inference(resolution, [status(thm)], [c_693, c_8])).
% 4.51/1.78  tff(c_82, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_177])).
% 4.51/1.78  tff(c_859, plain, (![A_177, B_178, C_179, D_180]: (k3_funct_2(A_177, B_178, C_179, D_180)=k1_funct_1(C_179, D_180) | ~m1_subset_1(D_180, A_177) | ~m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1(A_177, B_178))) | ~v1_funct_2(C_179, A_177, B_178) | ~v1_funct_1(C_179) | v1_xboole_0(A_177))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.51/1.78  tff(c_865, plain, (![B_178, C_179, B_167]: (k3_funct_2('#skF_3', B_178, C_179, '#skF_1'('#skF_3', B_167, '#skF_5'))=k1_funct_1(C_179, '#skF_1'('#skF_3', B_167, '#skF_5')) | ~m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_178))) | ~v1_funct_2(C_179, '#skF_3', B_178) | ~v1_funct_1(C_179) | v1_xboole_0('#skF_3') | v5_relat_1('#skF_5', B_167))), inference(resolution, [status(thm)], [c_697, c_859])).
% 4.51/1.78  tff(c_973, plain, (![B_194, C_195, B_196]: (k3_funct_2('#skF_3', B_194, C_195, '#skF_1'('#skF_3', B_196, '#skF_5'))=k1_funct_1(C_195, '#skF_1'('#skF_3', B_196, '#skF_5')) | ~m1_subset_1(C_195, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_194))) | ~v1_funct_2(C_195, '#skF_3', B_194) | ~v1_funct_1(C_195) | v5_relat_1('#skF_5', B_196))), inference(negUnitSimplification, [status(thm)], [c_82, c_865])).
% 4.51/1.78  tff(c_982, plain, (![B_196]: (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'('#skF_3', B_196, '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_196, '#skF_5')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | v5_relat_1('#skF_5', B_196))), inference(resolution, [status(thm)], [c_74, c_973])).
% 4.51/1.78  tff(c_1628, plain, (![B_269]: (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'('#skF_3', B_269, '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_269, '#skF_5')) | v5_relat_1('#skF_5', B_269))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_982])).
% 4.51/1.78  tff(c_72, plain, (![E_54]: (r2_hidden(k3_funct_2('#skF_3', '#skF_4', '#skF_5', E_54), '#skF_2') | ~m1_subset_1(E_54, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_177])).
% 4.51/1.78  tff(c_1661, plain, (![B_274]: (r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_274, '#skF_5')), '#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', B_274, '#skF_5'), '#skF_3') | v5_relat_1('#skF_5', B_274))), inference(superposition, [status(thm), theory('equality')], [c_1628, c_72])).
% 4.51/1.78  tff(c_594, plain, (![C_157, B_158]: (~r2_hidden(k1_funct_1(C_157, '#skF_1'(k1_relat_1(C_157), B_158, C_157)), B_158) | v1_funct_2(C_157, k1_relat_1(C_157), B_158) | ~v1_funct_1(C_157) | ~v1_relat_1(C_157))), inference(cnfTransformation, [status(thm)], [f_155])).
% 4.51/1.78  tff(c_597, plain, (![B_158]: (~r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_158, '#skF_5')), B_158) | v1_funct_2('#skF_5', k1_relat_1('#skF_5'), B_158) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_342, c_594])).
% 4.51/1.78  tff(c_599, plain, (![B_158]: (~r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_158, '#skF_5')), B_158) | v1_funct_2('#skF_5', '#skF_3', B_158))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_78, c_342, c_597])).
% 4.51/1.78  tff(c_1669, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3') | v5_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_1661, c_599])).
% 4.51/1.78  tff(c_1678, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_236, c_1669])).
% 4.51/1.78  tff(c_1680, plain, (~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_1678])).
% 4.51/1.78  tff(c_1720, plain, (v5_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_697, c_1680])).
% 4.51/1.78  tff(c_1729, plain, $false, inference(negUnitSimplification, [status(thm)], [c_236, c_1720])).
% 4.51/1.78  tff(c_1731, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3')), inference(splitRight, [status(thm)], [c_1678])).
% 4.51/1.78  tff(c_749, plain, (![C_169, B_170]: (~r2_hidden(k1_funct_1(C_169, '#skF_1'(k1_relat_1(C_169), B_170, C_169)), B_170) | m1_subset_1(C_169, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_169), B_170))) | ~v1_funct_1(C_169) | ~v1_relat_1(C_169))), inference(cnfTransformation, [status(thm)], [f_155])).
% 4.51/1.78  tff(c_752, plain, (![B_170]: (~r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_170, '#skF_5')), B_170) | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), B_170))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_342, c_749])).
% 4.51/1.78  tff(c_754, plain, (![B_170]: (~r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_170, '#skF_5')), B_170) | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_170))))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_78, c_342, c_752])).
% 4.51/1.78  tff(c_1665, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3') | v5_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_1661, c_754])).
% 4.51/1.78  tff(c_1675, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_236, c_1665])).
% 4.51/1.78  tff(c_1738, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1731, c_1675])).
% 4.51/1.78  tff(c_1772, plain, (v5_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_1738, c_20])).
% 4.51/1.78  tff(c_1812, plain, $false, inference(negUnitSimplification, [status(thm)], [c_236, c_1772])).
% 4.51/1.78  tff(c_1813, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_340])).
% 4.51/1.78  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.51/1.78  tff(c_1832, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1813, c_1813, c_4])).
% 4.51/1.78  tff(c_1843, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1832, c_74])).
% 4.51/1.78  tff(c_6, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.51/1.78  tff(c_161, plain, (![C_80, B_81, A_82]: (v5_relat_1(C_80, B_81) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_82, B_81))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.51/1.78  tff(c_170, plain, (![C_80, B_2]: (v5_relat_1(C_80, B_2) | ~m1_subset_1(C_80, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_161])).
% 4.51/1.78  tff(c_1912, plain, (![C_281, B_282]: (v5_relat_1(C_281, B_282) | ~m1_subset_1(C_281, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1813, c_170])).
% 4.51/1.78  tff(c_1915, plain, (![B_282]: (v5_relat_1('#skF_5', B_282))), inference(resolution, [status(thm)], [c_1843, c_1912])).
% 4.51/1.78  tff(c_1935, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1915, c_236])).
% 4.51/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.51/1.78  
% 4.51/1.78  Inference rules
% 4.51/1.78  ----------------------
% 4.51/1.78  #Ref     : 0
% 4.51/1.78  #Sup     : 400
% 4.51/1.78  #Fact    : 0
% 4.51/1.78  #Define  : 0
% 4.51/1.79  #Split   : 10
% 4.51/1.79  #Chain   : 0
% 4.51/1.79  #Close   : 0
% 4.51/1.79  
% 4.51/1.79  Ordering : KBO
% 4.51/1.79  
% 4.51/1.79  Simplification rules
% 4.51/1.79  ----------------------
% 4.51/1.79  #Subsume      : 54
% 4.51/1.79  #Demod        : 340
% 4.51/1.79  #Tautology    : 150
% 4.51/1.79  #SimpNegUnit  : 14
% 4.51/1.79  #BackRed      : 25
% 4.51/1.79  
% 4.51/1.79  #Partial instantiations: 0
% 4.51/1.79  #Strategies tried      : 1
% 4.51/1.79  
% 4.51/1.79  Timing (in seconds)
% 4.51/1.79  ----------------------
% 4.51/1.79  Preprocessing        : 0.37
% 4.51/1.79  Parsing              : 0.19
% 4.51/1.79  CNF conversion       : 0.03
% 4.51/1.79  Main loop            : 0.65
% 4.51/1.79  Inferencing          : 0.24
% 4.51/1.79  Reduction            : 0.20
% 4.51/1.79  Demodulation         : 0.13
% 4.51/1.79  BG Simplification    : 0.04
% 4.51/1.79  Subsumption          : 0.11
% 4.51/1.79  Abstraction          : 0.03
% 4.51/1.79  MUC search           : 0.00
% 4.51/1.79  Cooper               : 0.00
% 4.51/1.79  Total                : 1.05
% 4.51/1.79  Index Insertion      : 0.00
% 4.51/1.79  Index Deletion       : 0.00
% 4.51/1.79  Index Matching       : 0.00
% 4.51/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
