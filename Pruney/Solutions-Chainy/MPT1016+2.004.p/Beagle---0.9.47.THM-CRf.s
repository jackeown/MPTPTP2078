%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:41 EST 2020

% Result     : Theorem 3.56s
% Output     : CNFRefutation 3.56s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 274 expanded)
%              Number of leaves         :   36 ( 108 expanded)
%              Depth                    :   14
%              Number of atoms          :  204 ( 914 expanded)
%              Number of equality atoms :   44 ( 220 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

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

tff(f_106,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( v2_funct_1(B)
        <=> ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A)
                & k1_funct_1(B,C) = k1_funct_1(B,D) )
             => C = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_funct_2)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_64,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
      <=> ! [B,C] :
            ( ( r2_hidden(B,k1_relat_1(A))
              & r2_hidden(C,k1_relat_1(A))
              & k1_funct_1(A,B) = k1_funct_1(A,C) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_88,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(D)
          & r2_hidden(C,A) )
       => ( B = k1_xboole_0
          | k1_funct_1(k2_funct_1(D),k1_funct_1(D,C)) = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_78,plain,(
    ! [C_43,A_44,B_45] :
      ( v1_relat_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_87,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_78])).

tff(c_111,plain,(
    ! [C_55,A_56,B_57] :
      ( v4_relat_1(C_55,A_56)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_120,plain,(
    v4_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_111])).

tff(c_16,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k1_relat_1(B_12),A_11)
      | ~ v4_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_42,plain,
    ( '#skF_7' != '#skF_6'
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_61,plain,(
    ~ v2_funct_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_40,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_191,plain,(
    ! [A_77] :
      ( r2_hidden('#skF_3'(A_77),k1_relat_1(A_77))
      | v2_funct_1(A_77)
      | ~ v1_funct_1(A_77)
      | ~ v1_relat_1(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_8,plain,(
    ! [C_8,A_5,B_6] :
      ( r2_hidden(C_8,A_5)
      | ~ r2_hidden(C_8,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_309,plain,(
    ! [A_113,A_114] :
      ( r2_hidden('#skF_3'(A_113),A_114)
      | ~ m1_subset_1(k1_relat_1(A_113),k1_zfmisc_1(A_114))
      | v2_funct_1(A_113)
      | ~ v1_funct_1(A_113)
      | ~ v1_relat_1(A_113) ) ),
    inference(resolution,[status(thm)],[c_191,c_8])).

tff(c_314,plain,(
    ! [A_113,B_10] :
      ( r2_hidden('#skF_3'(A_113),B_10)
      | v2_funct_1(A_113)
      | ~ v1_funct_1(A_113)
      | ~ v1_relat_1(A_113)
      | ~ r1_tarski(k1_relat_1(A_113),B_10) ) ),
    inference(resolution,[status(thm)],[c_12,c_309])).

tff(c_142,plain,(
    ! [A_64] :
      ( '#skF_2'(A_64) != '#skF_3'(A_64)
      | v2_funct_1(A_64)
      | ~ v1_funct_1(A_64)
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_145,plain,
    ( '#skF_2'('#skF_5') != '#skF_3'('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_142,c_61])).

tff(c_148,plain,(
    '#skF_2'('#skF_5') != '#skF_3'('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_40,c_145])).

tff(c_208,plain,(
    ! [A_84] :
      ( r2_hidden('#skF_2'(A_84),k1_relat_1(A_84))
      | v2_funct_1(A_84)
      | ~ v1_funct_1(A_84)
      | ~ v1_relat_1(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_277,plain,(
    ! [A_103,A_104] :
      ( r2_hidden('#skF_2'(A_103),A_104)
      | ~ m1_subset_1(k1_relat_1(A_103),k1_zfmisc_1(A_104))
      | v2_funct_1(A_103)
      | ~ v1_funct_1(A_103)
      | ~ v1_relat_1(A_103) ) ),
    inference(resolution,[status(thm)],[c_208,c_8])).

tff(c_282,plain,(
    ! [A_103,B_10] :
      ( r2_hidden('#skF_2'(A_103),B_10)
      | v2_funct_1(A_103)
      | ~ v1_funct_1(A_103)
      | ~ v1_relat_1(A_103)
      | ~ r1_tarski(k1_relat_1(A_103),B_10) ) ),
    inference(resolution,[status(thm)],[c_12,c_277])).

tff(c_218,plain,(
    ! [A_91] :
      ( k1_funct_1(A_91,'#skF_2'(A_91)) = k1_funct_1(A_91,'#skF_3'(A_91))
      | v2_funct_1(A_91)
      | ~ v1_funct_1(A_91)
      | ~ v1_relat_1(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_60,plain,(
    ! [D_35,C_34] :
      ( v2_funct_1('#skF_5')
      | D_35 = C_34
      | k1_funct_1('#skF_5',D_35) != k1_funct_1('#skF_5',C_34)
      | ~ r2_hidden(D_35,'#skF_4')
      | ~ r2_hidden(C_34,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_105,plain,(
    ! [D_35,C_34] :
      ( D_35 = C_34
      | k1_funct_1('#skF_5',D_35) != k1_funct_1('#skF_5',C_34)
      | ~ r2_hidden(D_35,'#skF_4')
      | ~ r2_hidden(C_34,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_60])).

tff(c_224,plain,(
    ! [C_34] :
      ( C_34 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',C_34) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4')
      | ~ r2_hidden(C_34,'#skF_4')
      | v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_105])).

tff(c_233,plain,(
    ! [C_34] :
      ( C_34 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',C_34) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4')
      | ~ r2_hidden(C_34,'#skF_4')
      | v2_funct_1('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_40,c_224])).

tff(c_234,plain,(
    ! [C_34] :
      ( C_34 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',C_34) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4')
      | ~ r2_hidden(C_34,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_233])).

tff(c_360,plain,(
    ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_234])).

tff(c_363,plain,
    ( v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_282,c_360])).

tff(c_366,plain,
    ( v2_funct_1('#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_40,c_363])).

tff(c_367,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_366])).

tff(c_370,plain,
    ( ~ v4_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_367])).

tff(c_374,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_120,c_370])).

tff(c_375,plain,(
    ! [C_34] :
      ( C_34 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',C_34) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden(C_34,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_234])).

tff(c_462,plain,
    ( '#skF_2'('#skF_5') = '#skF_3'('#skF_5')
    | ~ r2_hidden('#skF_3'('#skF_5'),'#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_375])).

tff(c_463,plain,(
    ~ r2_hidden('#skF_3'('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_462])).

tff(c_475,plain,
    ( v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_314,c_463])).

tff(c_478,plain,
    ( v2_funct_1('#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_40,c_475])).

tff(c_479,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_478])).

tff(c_484,plain,
    ( ~ v4_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_479])).

tff(c_488,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_120,c_484])).

tff(c_490,plain,(
    v2_funct_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_46,plain,
    ( r2_hidden('#skF_7','#skF_4')
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_493,plain,(
    r2_hidden('#skF_7','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_490,c_46])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_497,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_493,c_2])).

tff(c_38,plain,(
    v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_44,plain,
    ( k1_funct_1('#skF_5','#skF_7') = k1_funct_1('#skF_5','#skF_6')
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_520,plain,(
    k1_funct_1('#skF_5','#skF_7') = k1_funct_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_490,c_44])).

tff(c_854,plain,(
    ! [D_249,C_250,B_251,A_252] :
      ( k1_funct_1(k2_funct_1(D_249),k1_funct_1(D_249,C_250)) = C_250
      | k1_xboole_0 = B_251
      | ~ r2_hidden(C_250,A_252)
      | ~ v2_funct_1(D_249)
      | ~ m1_subset_1(D_249,k1_zfmisc_1(k2_zfmisc_1(A_252,B_251)))
      | ~ v1_funct_2(D_249,A_252,B_251)
      | ~ v1_funct_1(D_249) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_955,plain,(
    ! [D_268,B_269] :
      ( k1_funct_1(k2_funct_1(D_268),k1_funct_1(D_268,'#skF_7')) = '#skF_7'
      | k1_xboole_0 = B_269
      | ~ v2_funct_1(D_268)
      | ~ m1_subset_1(D_268,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_269)))
      | ~ v1_funct_2(D_268,'#skF_4',B_269)
      | ~ v1_funct_1(D_268) ) ),
    inference(resolution,[status(thm)],[c_493,c_854])).

tff(c_960,plain,
    ( k1_funct_1(k2_funct_1('#skF_5'),k1_funct_1('#skF_5','#skF_7')) = '#skF_7'
    | k1_xboole_0 = '#skF_4'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_2('#skF_5','#skF_4','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_955])).

tff(c_964,plain,
    ( k1_funct_1(k2_funct_1('#skF_5'),k1_funct_1('#skF_5','#skF_6')) = '#skF_7'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_490,c_520,c_960])).

tff(c_965,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_964])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_968,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_965,c_6])).

tff(c_970,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_497,c_968])).

tff(c_972,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_964])).

tff(c_489,plain,(
    '#skF_7' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_971,plain,(
    k1_funct_1(k2_funct_1('#skF_5'),k1_funct_1('#skF_5','#skF_6')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_964])).

tff(c_48,plain,
    ( r2_hidden('#skF_6','#skF_4')
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_499,plain,(
    r2_hidden('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_490,c_48])).

tff(c_1015,plain,(
    ! [D_282,B_283] :
      ( k1_funct_1(k2_funct_1(D_282),k1_funct_1(D_282,'#skF_6')) = '#skF_6'
      | k1_xboole_0 = B_283
      | ~ v2_funct_1(D_282)
      | ~ m1_subset_1(D_282,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_283)))
      | ~ v1_funct_2(D_282,'#skF_4',B_283)
      | ~ v1_funct_1(D_282) ) ),
    inference(resolution,[status(thm)],[c_499,c_854])).

tff(c_1020,plain,
    ( k1_funct_1(k2_funct_1('#skF_5'),k1_funct_1('#skF_5','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_4'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_2('#skF_5','#skF_4','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_1015])).

tff(c_1024,plain,
    ( '#skF_7' = '#skF_6'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_490,c_971,c_1020])).

tff(c_1026,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_972,c_489,c_1024])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:00:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.56/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.56/1.61  
% 3.56/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.56/1.61  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3
% 3.56/1.61  
% 3.56/1.61  %Foreground sorts:
% 3.56/1.61  
% 3.56/1.61  
% 3.56/1.61  %Background operators:
% 3.56/1.61  
% 3.56/1.61  
% 3.56/1.61  %Foreground operators:
% 3.56/1.61  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.56/1.61  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.56/1.61  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.56/1.61  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.56/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.56/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.56/1.61  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.56/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.56/1.61  tff('#skF_7', type, '#skF_7': $i).
% 3.56/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.56/1.61  tff('#skF_5', type, '#skF_5': $i).
% 3.56/1.61  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.56/1.61  tff('#skF_6', type, '#skF_6': $i).
% 3.56/1.61  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.56/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.56/1.61  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.56/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.56/1.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.56/1.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.56/1.61  tff('#skF_4', type, '#skF_4': $i).
% 3.56/1.61  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.56/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.56/1.61  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.56/1.61  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.56/1.61  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.56/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.56/1.61  
% 3.56/1.62  tff(f_106, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) <=> (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_funct_2)).
% 3.56/1.62  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.56/1.62  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.56/1.62  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.56/1.62  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.56/1.62  tff(f_64, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_funct_1)).
% 3.56/1.62  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 3.56/1.62  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.56/1.62  tff(f_88, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(D) & r2_hidden(C, A)) => ((B = k1_xboole_0) | (k1_funct_1(k2_funct_1(D), k1_funct_1(D, C)) = C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_funct_2)).
% 3.56/1.62  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.56/1.62  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.56/1.62  tff(c_78, plain, (![C_43, A_44, B_45]: (v1_relat_1(C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.56/1.62  tff(c_87, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_36, c_78])).
% 3.56/1.62  tff(c_111, plain, (![C_55, A_56, B_57]: (v4_relat_1(C_55, A_56) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.56/1.62  tff(c_120, plain, (v4_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_36, c_111])).
% 3.56/1.62  tff(c_16, plain, (![B_12, A_11]: (r1_tarski(k1_relat_1(B_12), A_11) | ~v4_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.56/1.62  tff(c_42, plain, ('#skF_7'!='#skF_6' | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.56/1.62  tff(c_61, plain, (~v2_funct_1('#skF_5')), inference(splitLeft, [status(thm)], [c_42])).
% 3.56/1.62  tff(c_40, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.56/1.62  tff(c_12, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.56/1.62  tff(c_191, plain, (![A_77]: (r2_hidden('#skF_3'(A_77), k1_relat_1(A_77)) | v2_funct_1(A_77) | ~v1_funct_1(A_77) | ~v1_relat_1(A_77))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.56/1.62  tff(c_8, plain, (![C_8, A_5, B_6]: (r2_hidden(C_8, A_5) | ~r2_hidden(C_8, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.56/1.62  tff(c_309, plain, (![A_113, A_114]: (r2_hidden('#skF_3'(A_113), A_114) | ~m1_subset_1(k1_relat_1(A_113), k1_zfmisc_1(A_114)) | v2_funct_1(A_113) | ~v1_funct_1(A_113) | ~v1_relat_1(A_113))), inference(resolution, [status(thm)], [c_191, c_8])).
% 3.56/1.62  tff(c_314, plain, (![A_113, B_10]: (r2_hidden('#skF_3'(A_113), B_10) | v2_funct_1(A_113) | ~v1_funct_1(A_113) | ~v1_relat_1(A_113) | ~r1_tarski(k1_relat_1(A_113), B_10))), inference(resolution, [status(thm)], [c_12, c_309])).
% 3.56/1.62  tff(c_142, plain, (![A_64]: ('#skF_2'(A_64)!='#skF_3'(A_64) | v2_funct_1(A_64) | ~v1_funct_1(A_64) | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.56/1.62  tff(c_145, plain, ('#skF_2'('#skF_5')!='#skF_3'('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_142, c_61])).
% 3.56/1.62  tff(c_148, plain, ('#skF_2'('#skF_5')!='#skF_3'('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_87, c_40, c_145])).
% 3.56/1.62  tff(c_208, plain, (![A_84]: (r2_hidden('#skF_2'(A_84), k1_relat_1(A_84)) | v2_funct_1(A_84) | ~v1_funct_1(A_84) | ~v1_relat_1(A_84))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.56/1.62  tff(c_277, plain, (![A_103, A_104]: (r2_hidden('#skF_2'(A_103), A_104) | ~m1_subset_1(k1_relat_1(A_103), k1_zfmisc_1(A_104)) | v2_funct_1(A_103) | ~v1_funct_1(A_103) | ~v1_relat_1(A_103))), inference(resolution, [status(thm)], [c_208, c_8])).
% 3.56/1.62  tff(c_282, plain, (![A_103, B_10]: (r2_hidden('#skF_2'(A_103), B_10) | v2_funct_1(A_103) | ~v1_funct_1(A_103) | ~v1_relat_1(A_103) | ~r1_tarski(k1_relat_1(A_103), B_10))), inference(resolution, [status(thm)], [c_12, c_277])).
% 3.56/1.62  tff(c_218, plain, (![A_91]: (k1_funct_1(A_91, '#skF_2'(A_91))=k1_funct_1(A_91, '#skF_3'(A_91)) | v2_funct_1(A_91) | ~v1_funct_1(A_91) | ~v1_relat_1(A_91))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.56/1.62  tff(c_60, plain, (![D_35, C_34]: (v2_funct_1('#skF_5') | D_35=C_34 | k1_funct_1('#skF_5', D_35)!=k1_funct_1('#skF_5', C_34) | ~r2_hidden(D_35, '#skF_4') | ~r2_hidden(C_34, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.56/1.62  tff(c_105, plain, (![D_35, C_34]: (D_35=C_34 | k1_funct_1('#skF_5', D_35)!=k1_funct_1('#skF_5', C_34) | ~r2_hidden(D_35, '#skF_4') | ~r2_hidden(C_34, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_61, c_60])).
% 3.56/1.62  tff(c_224, plain, (![C_34]: (C_34='#skF_2'('#skF_5') | k1_funct_1('#skF_5', C_34)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4') | ~r2_hidden(C_34, '#skF_4') | v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_218, c_105])).
% 3.56/1.62  tff(c_233, plain, (![C_34]: (C_34='#skF_2'('#skF_5') | k1_funct_1('#skF_5', C_34)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4') | ~r2_hidden(C_34, '#skF_4') | v2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_40, c_224])).
% 3.56/1.62  tff(c_234, plain, (![C_34]: (C_34='#skF_2'('#skF_5') | k1_funct_1('#skF_5', C_34)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4') | ~r2_hidden(C_34, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_61, c_233])).
% 3.56/1.62  tff(c_360, plain, (~r2_hidden('#skF_2'('#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_234])).
% 3.56/1.62  tff(c_363, plain, (v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_282, c_360])).
% 3.56/1.63  tff(c_366, plain, (v2_funct_1('#skF_5') | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_87, c_40, c_363])).
% 3.56/1.63  tff(c_367, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_61, c_366])).
% 3.56/1.63  tff(c_370, plain, (~v4_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_16, c_367])).
% 3.56/1.63  tff(c_374, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_87, c_120, c_370])).
% 3.56/1.63  tff(c_375, plain, (![C_34]: (C_34='#skF_2'('#skF_5') | k1_funct_1('#skF_5', C_34)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden(C_34, '#skF_4'))), inference(splitRight, [status(thm)], [c_234])).
% 3.56/1.63  tff(c_462, plain, ('#skF_2'('#skF_5')='#skF_3'('#skF_5') | ~r2_hidden('#skF_3'('#skF_5'), '#skF_4')), inference(reflexivity, [status(thm), theory('equality')], [c_375])).
% 3.56/1.63  tff(c_463, plain, (~r2_hidden('#skF_3'('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_148, c_462])).
% 3.56/1.63  tff(c_475, plain, (v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_314, c_463])).
% 3.56/1.63  tff(c_478, plain, (v2_funct_1('#skF_5') | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_87, c_40, c_475])).
% 3.56/1.63  tff(c_479, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_61, c_478])).
% 3.56/1.63  tff(c_484, plain, (~v4_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_16, c_479])).
% 3.56/1.63  tff(c_488, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_87, c_120, c_484])).
% 3.56/1.63  tff(c_490, plain, (v2_funct_1('#skF_5')), inference(splitRight, [status(thm)], [c_42])).
% 3.56/1.63  tff(c_46, plain, (r2_hidden('#skF_7', '#skF_4') | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.56/1.63  tff(c_493, plain, (r2_hidden('#skF_7', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_490, c_46])).
% 3.56/1.63  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.56/1.63  tff(c_497, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_493, c_2])).
% 3.56/1.63  tff(c_38, plain, (v1_funct_2('#skF_5', '#skF_4', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.56/1.63  tff(c_44, plain, (k1_funct_1('#skF_5', '#skF_7')=k1_funct_1('#skF_5', '#skF_6') | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.56/1.63  tff(c_520, plain, (k1_funct_1('#skF_5', '#skF_7')=k1_funct_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_490, c_44])).
% 3.56/1.63  tff(c_854, plain, (![D_249, C_250, B_251, A_252]: (k1_funct_1(k2_funct_1(D_249), k1_funct_1(D_249, C_250))=C_250 | k1_xboole_0=B_251 | ~r2_hidden(C_250, A_252) | ~v2_funct_1(D_249) | ~m1_subset_1(D_249, k1_zfmisc_1(k2_zfmisc_1(A_252, B_251))) | ~v1_funct_2(D_249, A_252, B_251) | ~v1_funct_1(D_249))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.56/1.63  tff(c_955, plain, (![D_268, B_269]: (k1_funct_1(k2_funct_1(D_268), k1_funct_1(D_268, '#skF_7'))='#skF_7' | k1_xboole_0=B_269 | ~v2_funct_1(D_268) | ~m1_subset_1(D_268, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_269))) | ~v1_funct_2(D_268, '#skF_4', B_269) | ~v1_funct_1(D_268))), inference(resolution, [status(thm)], [c_493, c_854])).
% 3.56/1.63  tff(c_960, plain, (k1_funct_1(k2_funct_1('#skF_5'), k1_funct_1('#skF_5', '#skF_7'))='#skF_7' | k1_xboole_0='#skF_4' | ~v2_funct_1('#skF_5') | ~v1_funct_2('#skF_5', '#skF_4', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_36, c_955])).
% 3.56/1.63  tff(c_964, plain, (k1_funct_1(k2_funct_1('#skF_5'), k1_funct_1('#skF_5', '#skF_6'))='#skF_7' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_490, c_520, c_960])).
% 3.56/1.63  tff(c_965, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_964])).
% 3.56/1.63  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.56/1.63  tff(c_968, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_965, c_6])).
% 3.56/1.63  tff(c_970, plain, $false, inference(negUnitSimplification, [status(thm)], [c_497, c_968])).
% 3.56/1.63  tff(c_972, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_964])).
% 3.56/1.63  tff(c_489, plain, ('#skF_7'!='#skF_6'), inference(splitRight, [status(thm)], [c_42])).
% 3.56/1.63  tff(c_971, plain, (k1_funct_1(k2_funct_1('#skF_5'), k1_funct_1('#skF_5', '#skF_6'))='#skF_7'), inference(splitRight, [status(thm)], [c_964])).
% 3.56/1.63  tff(c_48, plain, (r2_hidden('#skF_6', '#skF_4') | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.56/1.63  tff(c_499, plain, (r2_hidden('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_490, c_48])).
% 3.56/1.63  tff(c_1015, plain, (![D_282, B_283]: (k1_funct_1(k2_funct_1(D_282), k1_funct_1(D_282, '#skF_6'))='#skF_6' | k1_xboole_0=B_283 | ~v2_funct_1(D_282) | ~m1_subset_1(D_282, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_283))) | ~v1_funct_2(D_282, '#skF_4', B_283) | ~v1_funct_1(D_282))), inference(resolution, [status(thm)], [c_499, c_854])).
% 3.56/1.63  tff(c_1020, plain, (k1_funct_1(k2_funct_1('#skF_5'), k1_funct_1('#skF_5', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_4' | ~v2_funct_1('#skF_5') | ~v1_funct_2('#skF_5', '#skF_4', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_36, c_1015])).
% 3.56/1.63  tff(c_1024, plain, ('#skF_7'='#skF_6' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_490, c_971, c_1020])).
% 3.56/1.63  tff(c_1026, plain, $false, inference(negUnitSimplification, [status(thm)], [c_972, c_489, c_1024])).
% 3.56/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.56/1.63  
% 3.56/1.63  Inference rules
% 3.56/1.63  ----------------------
% 3.56/1.63  #Ref     : 4
% 3.56/1.63  #Sup     : 211
% 3.56/1.63  #Fact    : 0
% 3.56/1.63  #Define  : 0
% 3.56/1.63  #Split   : 13
% 3.56/1.63  #Chain   : 0
% 3.56/1.63  #Close   : 0
% 3.56/1.63  
% 3.56/1.63  Ordering : KBO
% 3.56/1.63  
% 3.56/1.63  Simplification rules
% 3.56/1.63  ----------------------
% 3.56/1.63  #Subsume      : 35
% 3.56/1.63  #Demod        : 55
% 3.56/1.63  #Tautology    : 33
% 3.56/1.63  #SimpNegUnit  : 10
% 3.56/1.63  #BackRed      : 3
% 3.56/1.63  
% 3.56/1.63  #Partial instantiations: 0
% 3.56/1.63  #Strategies tried      : 1
% 3.56/1.63  
% 3.56/1.63  Timing (in seconds)
% 3.56/1.63  ----------------------
% 3.56/1.63  Preprocessing        : 0.33
% 3.56/1.63  Parsing              : 0.17
% 3.56/1.63  CNF conversion       : 0.02
% 3.56/1.63  Main loop            : 0.48
% 3.56/1.63  Inferencing          : 0.19
% 3.56/1.63  Reduction            : 0.13
% 3.56/1.63  Demodulation         : 0.08
% 3.56/1.63  BG Simplification    : 0.02
% 3.56/1.63  Subsumption          : 0.10
% 3.56/1.63  Abstraction          : 0.02
% 3.56/1.63  MUC search           : 0.00
% 3.56/1.63  Cooper               : 0.00
% 3.56/1.63  Total                : 0.85
% 3.56/1.63  Index Insertion      : 0.00
% 3.56/1.63  Index Deletion       : 0.00
% 3.56/1.63  Index Matching       : 0.00
% 3.56/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
