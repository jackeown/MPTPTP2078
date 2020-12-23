%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:21 EST 2020

% Result     : Theorem 12.27s
% Output     : CNFRefutation 12.27s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 616 expanded)
%              Number of leaves         :   34 ( 225 expanded)
%              Depth                    :   22
%              Number of atoms          :  215 (1940 expanded)
%              Number of equality atoms :   45 ( 460 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1 > #skF_6

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_101,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] :
                    ~ ( r2_hidden(E,A)
                      & D = k1_funct_1(C,E) ) )
         => k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_82,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_290,plain,(
    ! [A_91,B_92,C_93] :
      ( k2_relset_1(A_91,B_92,C_93) = k2_relat_1(C_93)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_299,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_290])).

tff(c_34,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_300,plain,(
    k2_relat_1('#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_34])).

tff(c_72,plain,(
    ! [C_43,A_44,B_45] :
      ( v1_relat_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_81,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_72])).

tff(c_114,plain,(
    ! [C_55,B_56,A_57] :
      ( v5_relat_1(C_55,B_56)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_57,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_123,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_114])).

tff(c_20,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k2_relat_1(B_12),A_11)
      | ~ v5_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_215,plain,(
    ! [A_83,B_84] :
      ( r2_hidden('#skF_1'(A_83,B_84),B_84)
      | r2_hidden('#skF_2'(A_83,B_84),A_83)
      | B_84 = A_83 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [C_8,A_5,B_6] :
      ( r2_hidden(C_8,A_5)
      | ~ r2_hidden(C_8,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_226,plain,(
    ! [A_83,B_84,A_5] :
      ( r2_hidden('#skF_1'(A_83,B_84),A_5)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(A_5))
      | r2_hidden('#skF_2'(A_83,B_84),A_83)
      | B_84 = A_83 ) ),
    inference(resolution,[status(thm)],[c_215,c_12])).

tff(c_44,plain,(
    ! [D_31] :
      ( r2_hidden('#skF_6'(D_31),'#skF_3')
      | ~ r2_hidden(D_31,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_42,plain,(
    ! [D_31] :
      ( k1_funct_1('#skF_5','#skF_6'(D_31)) = D_31
      | ~ r2_hidden(D_31,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_40,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_38,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_481,plain,(
    ! [D_123,C_124,A_125,B_126] :
      ( r2_hidden(k1_funct_1(D_123,C_124),k2_relset_1(A_125,B_126,D_123))
      | k1_xboole_0 = B_126
      | ~ r2_hidden(C_124,A_125)
      | ~ m1_subset_1(D_123,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126)))
      | ~ v1_funct_2(D_123,A_125,B_126)
      | ~ v1_funct_1(D_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_492,plain,(
    ! [C_124] :
      ( r2_hidden(k1_funct_1('#skF_5',C_124),k2_relat_1('#skF_5'))
      | k1_xboole_0 = '#skF_4'
      | ~ r2_hidden(C_124,'#skF_3')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_481])).

tff(c_499,plain,(
    ! [C_124] :
      ( r2_hidden(k1_funct_1('#skF_5',C_124),k2_relat_1('#skF_5'))
      | k1_xboole_0 = '#skF_4'
      | ~ r2_hidden(C_124,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_492])).

tff(c_502,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_499])).

tff(c_10,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_535,plain,(
    ! [A_4] : r1_tarski('#skF_4',A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_502,c_10])).

tff(c_715,plain,(
    ! [A_145,B_146,A_147] :
      ( r2_hidden('#skF_2'(A_145,B_146),A_147)
      | ~ m1_subset_1(A_145,k1_zfmisc_1(A_147))
      | r2_hidden('#skF_1'(A_145,B_146),B_146)
      | B_146 = A_145 ) ),
    inference(resolution,[status(thm)],[c_215,c_12])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2),B_2)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1072,plain,(
    ! [A_192,A_193] :
      ( ~ m1_subset_1(A_192,k1_zfmisc_1(A_193))
      | r2_hidden('#skF_1'(A_192,A_193),A_193)
      | A_193 = A_192 ) ),
    inference(resolution,[status(thm)],[c_715,c_4])).

tff(c_22,plain,(
    ! [B_14,A_13] :
      ( ~ r1_tarski(B_14,A_13)
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1096,plain,(
    ! [A_194,A_195] :
      ( ~ r1_tarski(A_194,'#skF_1'(A_195,A_194))
      | ~ m1_subset_1(A_195,k1_zfmisc_1(A_194))
      | A_195 = A_194 ) ),
    inference(resolution,[status(thm)],[c_1072,c_22])).

tff(c_1107,plain,(
    ! [A_196] :
      ( ~ m1_subset_1(A_196,k1_zfmisc_1('#skF_4'))
      | A_196 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_535,c_1096])).

tff(c_1170,plain,(
    ! [A_200] :
      ( A_200 = '#skF_4'
      | ~ r1_tarski(A_200,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_16,c_1107])).

tff(c_1194,plain,(
    ! [B_203] :
      ( k2_relat_1(B_203) = '#skF_4'
      | ~ v5_relat_1(B_203,'#skF_4')
      | ~ v1_relat_1(B_203) ) ),
    inference(resolution,[status(thm)],[c_20,c_1170])).

tff(c_1229,plain,
    ( k2_relat_1('#skF_5') = '#skF_4'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_123,c_1194])).

tff(c_1256,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_1229])).

tff(c_1258,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_300,c_1256])).

tff(c_1268,plain,(
    ! [C_207] :
      ( r2_hidden(k1_funct_1('#skF_5',C_207),k2_relat_1('#skF_5'))
      | ~ r2_hidden(C_207,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_499])).

tff(c_1338,plain,(
    ! [D_215] :
      ( r2_hidden(D_215,k2_relat_1('#skF_5'))
      | ~ r2_hidden('#skF_6'(D_215),'#skF_3')
      | ~ r2_hidden(D_215,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_1268])).

tff(c_1347,plain,(
    ! [D_31] :
      ( r2_hidden(D_31,k2_relat_1('#skF_5'))
      | ~ r2_hidden(D_31,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_1338])).

tff(c_8,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r2_hidden('#skF_2'(A_1,B_2),A_1)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1360,plain,(
    ! [D_217] :
      ( r2_hidden(D_217,k2_relat_1('#skF_5'))
      | ~ r2_hidden(D_217,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_1338])).

tff(c_1732,plain,(
    ! [D_245,A_246] :
      ( r2_hidden(D_245,A_246)
      | ~ m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1(A_246))
      | ~ r2_hidden(D_245,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1360,c_12])).

tff(c_1737,plain,(
    ! [D_247,B_248] :
      ( r2_hidden(D_247,B_248)
      | ~ r2_hidden(D_247,'#skF_4')
      | ~ r1_tarski(k2_relat_1('#skF_5'),B_248) ) ),
    inference(resolution,[status(thm)],[c_16,c_1732])).

tff(c_3546,plain,(
    ! [B_515,B_516] :
      ( r2_hidden('#skF_2'('#skF_4',B_515),B_516)
      | ~ r1_tarski(k2_relat_1('#skF_5'),B_516)
      | r2_hidden('#skF_1'('#skF_4',B_515),B_515)
      | B_515 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_8,c_1737])).

tff(c_3590,plain,(
    ! [B_517] :
      ( ~ r1_tarski(k2_relat_1('#skF_5'),B_517)
      | r2_hidden('#skF_1'('#skF_4',B_517),B_517)
      | B_517 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_3546,c_4])).

tff(c_3771,plain,(
    ! [B_524,A_525] :
      ( r2_hidden('#skF_1'('#skF_4',B_524),A_525)
      | ~ m1_subset_1(B_524,k1_zfmisc_1(A_525))
      | ~ r1_tarski(k2_relat_1('#skF_5'),B_524)
      | B_524 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_3590,c_12])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),A_1)
      | ~ r2_hidden('#skF_2'(A_1,B_2),B_2)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3861,plain,(
    ! [B_538] :
      ( ~ r2_hidden('#skF_2'('#skF_4',B_538),B_538)
      | ~ m1_subset_1(B_538,k1_zfmisc_1('#skF_4'))
      | ~ r1_tarski(k2_relat_1('#skF_5'),B_538)
      | B_538 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_3771,c_2])).

tff(c_3911,plain,
    ( ~ m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ r1_tarski(k2_relat_1('#skF_5'),k2_relat_1('#skF_5'))
    | k2_relat_1('#skF_5') = '#skF_4'
    | ~ r2_hidden('#skF_2'('#skF_4',k2_relat_1('#skF_5')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_1347,c_3861])).

tff(c_3936,plain,
    ( ~ m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ r1_tarski(k2_relat_1('#skF_5'),k2_relat_1('#skF_5'))
    | ~ r2_hidden('#skF_2'('#skF_4',k2_relat_1('#skF_5')),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_300,c_3911])).

tff(c_3969,plain,(
    ~ r2_hidden('#skF_2'('#skF_4',k2_relat_1('#skF_5')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3936])).

tff(c_3986,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_1'('#skF_4',k2_relat_1('#skF_5')),A_5)
      | ~ m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1(A_5))
      | k2_relat_1('#skF_5') = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_226,c_3969])).

tff(c_4117,plain,(
    ! [A_554] :
      ( r2_hidden('#skF_1'('#skF_4',k2_relat_1('#skF_5')),A_554)
      | ~ m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1(A_554)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_300,c_3986])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r2_hidden('#skF_2'(A_1,B_2),A_1)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3990,plain,
    ( ~ r2_hidden('#skF_1'('#skF_4',k2_relat_1('#skF_5')),'#skF_4')
    | k2_relat_1('#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6,c_3969])).

tff(c_4009,plain,(
    ~ r2_hidden('#skF_1'('#skF_4',k2_relat_1('#skF_5')),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_300,c_3990])).

tff(c_4141,plain,(
    ~ m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_4117,c_4009])).

tff(c_4158,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_4141])).

tff(c_4161,plain,
    ( ~ v5_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_20,c_4158])).

tff(c_4165,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_123,c_4161])).

tff(c_4166,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),k2_relat_1('#skF_5'))
    | ~ m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_3936])).

tff(c_4181,plain,(
    ~ m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_4166])).

tff(c_4185,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_4181])).

tff(c_4195,plain,
    ( ~ v5_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_20,c_4185])).

tff(c_4199,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_123,c_4195])).

tff(c_4201,plain,(
    m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_4166])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,B_10)
      | ~ m1_subset_1(A_9,k1_zfmisc_1(B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4265,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_4201,c_14])).

tff(c_1596,plain,(
    ! [A_228,B_229,A_230] :
      ( r2_hidden('#skF_2'(A_228,B_229),A_230)
      | ~ m1_subset_1(A_228,k1_zfmisc_1(A_230))
      | r2_hidden('#skF_1'(A_228,B_229),B_229)
      | B_229 = A_228 ) ),
    inference(resolution,[status(thm)],[c_215,c_12])).

tff(c_1618,plain,(
    ! [A_228,A_230] :
      ( ~ m1_subset_1(A_228,k1_zfmisc_1(A_230))
      | r2_hidden('#skF_1'(A_228,A_230),A_230)
      | A_230 = A_228 ) ),
    inference(resolution,[status(thm)],[c_1596,c_4])).

tff(c_1768,plain,(
    ! [A_228,B_248] :
      ( r2_hidden('#skF_1'(A_228,'#skF_4'),B_248)
      | ~ r1_tarski(k2_relat_1('#skF_5'),B_248)
      | ~ m1_subset_1(A_228,k1_zfmisc_1('#skF_4'))
      | A_228 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_1618,c_1737])).

tff(c_412,plain,(
    ! [A_107,B_108] :
      ( ~ r2_hidden('#skF_1'(A_107,B_108),A_107)
      | r2_hidden('#skF_2'(A_107,B_108),A_107)
      | B_108 = A_107 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1684,plain,(
    ! [A_239,B_240,A_241] :
      ( r2_hidden('#skF_2'(A_239,B_240),A_241)
      | ~ m1_subset_1(A_239,k1_zfmisc_1(A_241))
      | ~ r2_hidden('#skF_1'(A_239,B_240),A_239)
      | B_240 = A_239 ) ),
    inference(resolution,[status(thm)],[c_412,c_12])).

tff(c_12702,plain,(
    ! [B_1272,A_1273] :
      ( r2_hidden('#skF_2'(k2_relat_1('#skF_5'),B_1272),A_1273)
      | ~ m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1(A_1273))
      | k2_relat_1('#skF_5') = B_1272
      | ~ r2_hidden('#skF_1'(k2_relat_1('#skF_5'),B_1272),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1347,c_1684])).

tff(c_1382,plain,(
    ! [B_2] :
      ( ~ r2_hidden('#skF_2'(k2_relat_1('#skF_5'),B_2),B_2)
      | k2_relat_1('#skF_5') = B_2
      | ~ r2_hidden('#skF_1'(k2_relat_1('#skF_5'),B_2),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1360,c_2])).

tff(c_12779,plain,(
    ! [A_1274] :
      ( ~ m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1(A_1274))
      | k2_relat_1('#skF_5') = A_1274
      | ~ r2_hidden('#skF_1'(k2_relat_1('#skF_5'),A_1274),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_12702,c_1382])).

tff(c_12865,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | ~ m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4'))
    | k2_relat_1('#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1768,c_12779])).

tff(c_12952,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4201,c_4265,c_12865])).

tff(c_12954,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_300,c_12952])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:01:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.27/4.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.27/4.47  
% 12.27/4.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.27/4.48  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1 > #skF_6
% 12.27/4.48  
% 12.27/4.48  %Foreground sorts:
% 12.27/4.48  
% 12.27/4.48  
% 12.27/4.48  %Background operators:
% 12.27/4.48  
% 12.27/4.48  
% 12.27/4.48  %Foreground operators:
% 12.27/4.48  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 12.27/4.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.27/4.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.27/4.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.27/4.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.27/4.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.27/4.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 12.27/4.48  tff('#skF_5', type, '#skF_5': $i).
% 12.27/4.48  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 12.27/4.48  tff('#skF_3', type, '#skF_3': $i).
% 12.27/4.48  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 12.27/4.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.27/4.48  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 12.27/4.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.27/4.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.27/4.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.27/4.48  tff('#skF_4', type, '#skF_4': $i).
% 12.27/4.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.27/4.48  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 12.27/4.48  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 12.27/4.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 12.27/4.48  tff('#skF_6', type, '#skF_6': $i > $i).
% 12.27/4.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.27/4.48  
% 12.27/4.50  tff(f_101, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_2)).
% 12.27/4.50  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 12.27/4.50  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 12.27/4.50  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 12.27/4.50  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 12.27/4.50  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 12.27/4.50  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 12.27/4.50  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 12.27/4.50  tff(f_82, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 12.27/4.50  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 12.27/4.50  tff(f_56, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 12.27/4.50  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 12.27/4.50  tff(c_290, plain, (![A_91, B_92, C_93]: (k2_relset_1(A_91, B_92, C_93)=k2_relat_1(C_93) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 12.27/4.50  tff(c_299, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_36, c_290])).
% 12.27/4.50  tff(c_34, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_101])).
% 12.27/4.50  tff(c_300, plain, (k2_relat_1('#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_299, c_34])).
% 12.27/4.50  tff(c_72, plain, (![C_43, A_44, B_45]: (v1_relat_1(C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 12.27/4.50  tff(c_81, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_36, c_72])).
% 12.27/4.50  tff(c_114, plain, (![C_55, B_56, A_57]: (v5_relat_1(C_55, B_56) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_57, B_56))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 12.27/4.50  tff(c_123, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_36, c_114])).
% 12.27/4.50  tff(c_20, plain, (![B_12, A_11]: (r1_tarski(k2_relat_1(B_12), A_11) | ~v5_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 12.27/4.50  tff(c_16, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.27/4.50  tff(c_215, plain, (![A_83, B_84]: (r2_hidden('#skF_1'(A_83, B_84), B_84) | r2_hidden('#skF_2'(A_83, B_84), A_83) | B_84=A_83)), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.27/4.50  tff(c_12, plain, (![C_8, A_5, B_6]: (r2_hidden(C_8, A_5) | ~r2_hidden(C_8, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.27/4.50  tff(c_226, plain, (![A_83, B_84, A_5]: (r2_hidden('#skF_1'(A_83, B_84), A_5) | ~m1_subset_1(B_84, k1_zfmisc_1(A_5)) | r2_hidden('#skF_2'(A_83, B_84), A_83) | B_84=A_83)), inference(resolution, [status(thm)], [c_215, c_12])).
% 12.27/4.50  tff(c_44, plain, (![D_31]: (r2_hidden('#skF_6'(D_31), '#skF_3') | ~r2_hidden(D_31, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 12.27/4.50  tff(c_42, plain, (![D_31]: (k1_funct_1('#skF_5', '#skF_6'(D_31))=D_31 | ~r2_hidden(D_31, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 12.27/4.50  tff(c_40, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_101])).
% 12.27/4.50  tff(c_38, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 12.27/4.50  tff(c_481, plain, (![D_123, C_124, A_125, B_126]: (r2_hidden(k1_funct_1(D_123, C_124), k2_relset_1(A_125, B_126, D_123)) | k1_xboole_0=B_126 | ~r2_hidden(C_124, A_125) | ~m1_subset_1(D_123, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))) | ~v1_funct_2(D_123, A_125, B_126) | ~v1_funct_1(D_123))), inference(cnfTransformation, [status(thm)], [f_82])).
% 12.27/4.50  tff(c_492, plain, (![C_124]: (r2_hidden(k1_funct_1('#skF_5', C_124), k2_relat_1('#skF_5')) | k1_xboole_0='#skF_4' | ~r2_hidden(C_124, '#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_299, c_481])).
% 12.27/4.50  tff(c_499, plain, (![C_124]: (r2_hidden(k1_funct_1('#skF_5', C_124), k2_relat_1('#skF_5')) | k1_xboole_0='#skF_4' | ~r2_hidden(C_124, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_492])).
% 12.27/4.50  tff(c_502, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_499])).
% 12.27/4.50  tff(c_10, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 12.27/4.50  tff(c_535, plain, (![A_4]: (r1_tarski('#skF_4', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_502, c_10])).
% 12.27/4.50  tff(c_715, plain, (![A_145, B_146, A_147]: (r2_hidden('#skF_2'(A_145, B_146), A_147) | ~m1_subset_1(A_145, k1_zfmisc_1(A_147)) | r2_hidden('#skF_1'(A_145, B_146), B_146) | B_146=A_145)), inference(resolution, [status(thm)], [c_215, c_12])).
% 12.27/4.50  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | ~r2_hidden('#skF_2'(A_1, B_2), B_2) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.27/4.50  tff(c_1072, plain, (![A_192, A_193]: (~m1_subset_1(A_192, k1_zfmisc_1(A_193)) | r2_hidden('#skF_1'(A_192, A_193), A_193) | A_193=A_192)), inference(resolution, [status(thm)], [c_715, c_4])).
% 12.27/4.50  tff(c_22, plain, (![B_14, A_13]: (~r1_tarski(B_14, A_13) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_56])).
% 12.27/4.50  tff(c_1096, plain, (![A_194, A_195]: (~r1_tarski(A_194, '#skF_1'(A_195, A_194)) | ~m1_subset_1(A_195, k1_zfmisc_1(A_194)) | A_195=A_194)), inference(resolution, [status(thm)], [c_1072, c_22])).
% 12.27/4.50  tff(c_1107, plain, (![A_196]: (~m1_subset_1(A_196, k1_zfmisc_1('#skF_4')) | A_196='#skF_4')), inference(resolution, [status(thm)], [c_535, c_1096])).
% 12.27/4.50  tff(c_1170, plain, (![A_200]: (A_200='#skF_4' | ~r1_tarski(A_200, '#skF_4'))), inference(resolution, [status(thm)], [c_16, c_1107])).
% 12.27/4.50  tff(c_1194, plain, (![B_203]: (k2_relat_1(B_203)='#skF_4' | ~v5_relat_1(B_203, '#skF_4') | ~v1_relat_1(B_203))), inference(resolution, [status(thm)], [c_20, c_1170])).
% 12.27/4.50  tff(c_1229, plain, (k2_relat_1('#skF_5')='#skF_4' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_123, c_1194])).
% 12.27/4.50  tff(c_1256, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_81, c_1229])).
% 12.27/4.50  tff(c_1258, plain, $false, inference(negUnitSimplification, [status(thm)], [c_300, c_1256])).
% 12.27/4.50  tff(c_1268, plain, (![C_207]: (r2_hidden(k1_funct_1('#skF_5', C_207), k2_relat_1('#skF_5')) | ~r2_hidden(C_207, '#skF_3'))), inference(splitRight, [status(thm)], [c_499])).
% 12.27/4.50  tff(c_1338, plain, (![D_215]: (r2_hidden(D_215, k2_relat_1('#skF_5')) | ~r2_hidden('#skF_6'(D_215), '#skF_3') | ~r2_hidden(D_215, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_42, c_1268])).
% 12.27/4.50  tff(c_1347, plain, (![D_31]: (r2_hidden(D_31, k2_relat_1('#skF_5')) | ~r2_hidden(D_31, '#skF_4'))), inference(resolution, [status(thm)], [c_44, c_1338])).
% 12.27/4.50  tff(c_8, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r2_hidden('#skF_2'(A_1, B_2), A_1) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.27/4.50  tff(c_1360, plain, (![D_217]: (r2_hidden(D_217, k2_relat_1('#skF_5')) | ~r2_hidden(D_217, '#skF_4'))), inference(resolution, [status(thm)], [c_44, c_1338])).
% 12.27/4.50  tff(c_1732, plain, (![D_245, A_246]: (r2_hidden(D_245, A_246) | ~m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1(A_246)) | ~r2_hidden(D_245, '#skF_4'))), inference(resolution, [status(thm)], [c_1360, c_12])).
% 12.27/4.50  tff(c_1737, plain, (![D_247, B_248]: (r2_hidden(D_247, B_248) | ~r2_hidden(D_247, '#skF_4') | ~r1_tarski(k2_relat_1('#skF_5'), B_248))), inference(resolution, [status(thm)], [c_16, c_1732])).
% 12.27/4.50  tff(c_3546, plain, (![B_515, B_516]: (r2_hidden('#skF_2'('#skF_4', B_515), B_516) | ~r1_tarski(k2_relat_1('#skF_5'), B_516) | r2_hidden('#skF_1'('#skF_4', B_515), B_515) | B_515='#skF_4')), inference(resolution, [status(thm)], [c_8, c_1737])).
% 12.27/4.50  tff(c_3590, plain, (![B_517]: (~r1_tarski(k2_relat_1('#skF_5'), B_517) | r2_hidden('#skF_1'('#skF_4', B_517), B_517) | B_517='#skF_4')), inference(resolution, [status(thm)], [c_3546, c_4])).
% 12.27/4.50  tff(c_3771, plain, (![B_524, A_525]: (r2_hidden('#skF_1'('#skF_4', B_524), A_525) | ~m1_subset_1(B_524, k1_zfmisc_1(A_525)) | ~r1_tarski(k2_relat_1('#skF_5'), B_524) | B_524='#skF_4')), inference(resolution, [status(thm)], [c_3590, c_12])).
% 12.27/4.50  tff(c_2, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), A_1) | ~r2_hidden('#skF_2'(A_1, B_2), B_2) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.27/4.50  tff(c_3861, plain, (![B_538]: (~r2_hidden('#skF_2'('#skF_4', B_538), B_538) | ~m1_subset_1(B_538, k1_zfmisc_1('#skF_4')) | ~r1_tarski(k2_relat_1('#skF_5'), B_538) | B_538='#skF_4')), inference(resolution, [status(thm)], [c_3771, c_2])).
% 12.27/4.50  tff(c_3911, plain, (~m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4')) | ~r1_tarski(k2_relat_1('#skF_5'), k2_relat_1('#skF_5')) | k2_relat_1('#skF_5')='#skF_4' | ~r2_hidden('#skF_2'('#skF_4', k2_relat_1('#skF_5')), '#skF_4')), inference(resolution, [status(thm)], [c_1347, c_3861])).
% 12.27/4.50  tff(c_3936, plain, (~m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4')) | ~r1_tarski(k2_relat_1('#skF_5'), k2_relat_1('#skF_5')) | ~r2_hidden('#skF_2'('#skF_4', k2_relat_1('#skF_5')), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_300, c_3911])).
% 12.27/4.50  tff(c_3969, plain, (~r2_hidden('#skF_2'('#skF_4', k2_relat_1('#skF_5')), '#skF_4')), inference(splitLeft, [status(thm)], [c_3936])).
% 12.27/4.50  tff(c_3986, plain, (![A_5]: (r2_hidden('#skF_1'('#skF_4', k2_relat_1('#skF_5')), A_5) | ~m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1(A_5)) | k2_relat_1('#skF_5')='#skF_4')), inference(resolution, [status(thm)], [c_226, c_3969])).
% 12.27/4.50  tff(c_4117, plain, (![A_554]: (r2_hidden('#skF_1'('#skF_4', k2_relat_1('#skF_5')), A_554) | ~m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1(A_554)))), inference(negUnitSimplification, [status(thm)], [c_300, c_3986])).
% 12.27/4.50  tff(c_6, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), A_1) | r2_hidden('#skF_2'(A_1, B_2), A_1) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.27/4.50  tff(c_3990, plain, (~r2_hidden('#skF_1'('#skF_4', k2_relat_1('#skF_5')), '#skF_4') | k2_relat_1('#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_6, c_3969])).
% 12.27/4.50  tff(c_4009, plain, (~r2_hidden('#skF_1'('#skF_4', k2_relat_1('#skF_5')), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_300, c_3990])).
% 12.27/4.50  tff(c_4141, plain, (~m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_4117, c_4009])).
% 12.27/4.50  tff(c_4158, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_16, c_4141])).
% 12.27/4.50  tff(c_4161, plain, (~v5_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_20, c_4158])).
% 12.27/4.50  tff(c_4165, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_81, c_123, c_4161])).
% 12.27/4.50  tff(c_4166, plain, (~r1_tarski(k2_relat_1('#skF_5'), k2_relat_1('#skF_5')) | ~m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_3936])).
% 12.27/4.50  tff(c_4181, plain, (~m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_4166])).
% 12.27/4.50  tff(c_4185, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_16, c_4181])).
% 12.27/4.50  tff(c_4195, plain, (~v5_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_20, c_4185])).
% 12.27/4.50  tff(c_4199, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_81, c_123, c_4195])).
% 12.27/4.50  tff(c_4201, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_4166])).
% 12.27/4.50  tff(c_14, plain, (![A_9, B_10]: (r1_tarski(A_9, B_10) | ~m1_subset_1(A_9, k1_zfmisc_1(B_10)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.27/4.50  tff(c_4265, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_4201, c_14])).
% 12.27/4.50  tff(c_1596, plain, (![A_228, B_229, A_230]: (r2_hidden('#skF_2'(A_228, B_229), A_230) | ~m1_subset_1(A_228, k1_zfmisc_1(A_230)) | r2_hidden('#skF_1'(A_228, B_229), B_229) | B_229=A_228)), inference(resolution, [status(thm)], [c_215, c_12])).
% 12.27/4.50  tff(c_1618, plain, (![A_228, A_230]: (~m1_subset_1(A_228, k1_zfmisc_1(A_230)) | r2_hidden('#skF_1'(A_228, A_230), A_230) | A_230=A_228)), inference(resolution, [status(thm)], [c_1596, c_4])).
% 12.27/4.50  tff(c_1768, plain, (![A_228, B_248]: (r2_hidden('#skF_1'(A_228, '#skF_4'), B_248) | ~r1_tarski(k2_relat_1('#skF_5'), B_248) | ~m1_subset_1(A_228, k1_zfmisc_1('#skF_4')) | A_228='#skF_4')), inference(resolution, [status(thm)], [c_1618, c_1737])).
% 12.27/4.50  tff(c_412, plain, (![A_107, B_108]: (~r2_hidden('#skF_1'(A_107, B_108), A_107) | r2_hidden('#skF_2'(A_107, B_108), A_107) | B_108=A_107)), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.27/4.50  tff(c_1684, plain, (![A_239, B_240, A_241]: (r2_hidden('#skF_2'(A_239, B_240), A_241) | ~m1_subset_1(A_239, k1_zfmisc_1(A_241)) | ~r2_hidden('#skF_1'(A_239, B_240), A_239) | B_240=A_239)), inference(resolution, [status(thm)], [c_412, c_12])).
% 12.27/4.50  tff(c_12702, plain, (![B_1272, A_1273]: (r2_hidden('#skF_2'(k2_relat_1('#skF_5'), B_1272), A_1273) | ~m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1(A_1273)) | k2_relat_1('#skF_5')=B_1272 | ~r2_hidden('#skF_1'(k2_relat_1('#skF_5'), B_1272), '#skF_4'))), inference(resolution, [status(thm)], [c_1347, c_1684])).
% 12.27/4.50  tff(c_1382, plain, (![B_2]: (~r2_hidden('#skF_2'(k2_relat_1('#skF_5'), B_2), B_2) | k2_relat_1('#skF_5')=B_2 | ~r2_hidden('#skF_1'(k2_relat_1('#skF_5'), B_2), '#skF_4'))), inference(resolution, [status(thm)], [c_1360, c_2])).
% 12.27/4.50  tff(c_12779, plain, (![A_1274]: (~m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1(A_1274)) | k2_relat_1('#skF_5')=A_1274 | ~r2_hidden('#skF_1'(k2_relat_1('#skF_5'), A_1274), '#skF_4'))), inference(resolution, [status(thm)], [c_12702, c_1382])).
% 12.27/4.50  tff(c_12865, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | ~m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4')) | k2_relat_1('#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_1768, c_12779])).
% 12.27/4.50  tff(c_12952, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4201, c_4265, c_12865])).
% 12.27/4.50  tff(c_12954, plain, $false, inference(negUnitSimplification, [status(thm)], [c_300, c_12952])).
% 12.27/4.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.27/4.50  
% 12.27/4.50  Inference rules
% 12.27/4.50  ----------------------
% 12.27/4.50  #Ref     : 0
% 12.27/4.50  #Sup     : 2491
% 12.27/4.50  #Fact    : 2
% 12.27/4.50  #Define  : 0
% 12.27/4.50  #Split   : 24
% 12.27/4.50  #Chain   : 0
% 12.27/4.50  #Close   : 0
% 12.27/4.50  
% 12.27/4.50  Ordering : KBO
% 12.27/4.50  
% 12.27/4.50  Simplification rules
% 12.27/4.50  ----------------------
% 12.27/4.50  #Subsume      : 1199
% 12.27/4.50  #Demod        : 1351
% 12.27/4.50  #Tautology    : 196
% 12.27/4.50  #SimpNegUnit  : 240
% 12.27/4.50  #BackRed      : 362
% 12.27/4.50  
% 12.27/4.50  #Partial instantiations: 0
% 12.27/4.50  #Strategies tried      : 1
% 12.27/4.50  
% 12.27/4.50  Timing (in seconds)
% 12.27/4.50  ----------------------
% 12.27/4.50  Preprocessing        : 0.31
% 12.27/4.50  Parsing              : 0.17
% 12.27/4.50  CNF conversion       : 0.02
% 12.27/4.50  Main loop            : 3.43
% 12.27/4.50  Inferencing          : 0.97
% 12.27/4.50  Reduction            : 0.88
% 12.27/4.50  Demodulation         : 0.53
% 12.27/4.50  BG Simplification    : 0.06
% 12.27/4.50  Subsumption          : 1.28
% 12.27/4.50  Abstraction          : 0.09
% 12.27/4.50  MUC search           : 0.00
% 12.27/4.50  Cooper               : 0.00
% 12.27/4.50  Total                : 3.78
% 12.27/4.50  Index Insertion      : 0.00
% 12.27/4.50  Index Deletion       : 0.00
% 12.27/4.50  Index Matching       : 0.00
% 12.27/4.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
