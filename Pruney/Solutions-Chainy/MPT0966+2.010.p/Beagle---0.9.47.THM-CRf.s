%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:09 EST 2020

% Result     : Theorem 3.56s
% Output     : CNFRefutation 3.56s
% Verified   : 
% Statistics : Number of formulae       :  206 (2516 expanded)
%              Number of leaves         :   28 ( 796 expanded)
%              Depth                    :   16
%              Number of atoms          :  342 (7242 expanded)
%              Number of equality atoms :  145 (2508 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_95,negated_conjecture,(
    ~ ! [A,B,C,D] :
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

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
     => ( r1_tarski(k2_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_75,axiom,(
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

tff(f_36,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1290,plain,(
    ! [A_205,B_206,C_207] :
      ( k2_relset_1(A_205,B_206,C_207) = k2_relat_1(C_207)
      | ~ m1_subset_1(C_207,k1_zfmisc_1(k2_zfmisc_1(A_205,B_206))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1300,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_1290])).

tff(c_36,plain,(
    r1_tarski(k2_relset_1('#skF_1','#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1301,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1300,c_36])).

tff(c_1355,plain,(
    ! [D_219,C_220,B_221,A_222] :
      ( m1_subset_1(D_219,k1_zfmisc_1(k2_zfmisc_1(C_220,B_221)))
      | ~ r1_tarski(k2_relat_1(D_219),B_221)
      | ~ m1_subset_1(D_219,k1_zfmisc_1(k2_zfmisc_1(C_220,A_222))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1371,plain,(
    ! [B_224] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_224)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_224) ) ),
    inference(resolution,[status(thm)],[c_38,c_1355])).

tff(c_42,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_32,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_44,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_32])).

tff(c_528,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_548,plain,(
    ! [A_111,B_112,C_113] :
      ( k2_relset_1(A_111,B_112,C_113) = k2_relat_1(C_113)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_558,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_548])).

tff(c_559,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_558,c_36])).

tff(c_612,plain,(
    ! [D_125,C_126,B_127,A_128] :
      ( m1_subset_1(D_125,k1_zfmisc_1(k2_zfmisc_1(C_126,B_127)))
      | ~ r1_tarski(k2_relat_1(D_125),B_127)
      | ~ m1_subset_1(D_125,k1_zfmisc_1(k2_zfmisc_1(C_126,A_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_636,plain,(
    ! [B_130] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_130)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_130) ) ),
    inference(resolution,[status(thm)],[c_38,c_612])).

tff(c_14,plain,(
    ! [A_7,B_8,C_9] :
      ( k1_relset_1(A_7,B_8,C_9) = k1_relat_1(C_9)
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1006,plain,(
    ! [B_169] :
      ( k1_relset_1('#skF_1',B_169,'#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_169) ) ),
    inference(resolution,[status(thm)],[c_636,c_14])).

tff(c_1015,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_559,c_1006])).

tff(c_619,plain,(
    ! [B_127] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_127)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_127) ) ),
    inference(resolution,[status(thm)],[c_38,c_612])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_674,plain,(
    ! [B_134] :
      ( k1_relset_1('#skF_1',B_134,'#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_134) ) ),
    inference(resolution,[status(thm)],[c_636,c_14])).

tff(c_678,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_559,c_674])).

tff(c_695,plain,(
    ! [B_138,C_139,A_140] :
      ( k1_xboole_0 = B_138
      | v1_funct_2(C_139,A_140,B_138)
      | k1_relset_1(A_140,B_138,C_139) != A_140
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_140,B_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_744,plain,(
    ! [B_147] :
      ( k1_xboole_0 = B_147
      | v1_funct_2('#skF_4','#skF_1',B_147)
      | k1_relset_1('#skF_1',B_147,'#skF_4') != '#skF_1'
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_147) ) ),
    inference(resolution,[status(thm)],[c_619,c_695])).

tff(c_747,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4','#skF_1','#skF_3')
    | k1_relset_1('#skF_1','#skF_3','#skF_4') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_559,c_744])).

tff(c_749,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4','#skF_1','#skF_3')
    | k1_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_678,c_747])).

tff(c_750,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_528,c_749])).

tff(c_751,plain,(
    k1_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_750])).

tff(c_34,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_40,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_529,plain,(
    ! [A_106,B_107,C_108] :
      ( k1_relset_1(A_106,B_107,C_108) = k1_relat_1(C_108)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_539,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_529])).

tff(c_766,plain,(
    ! [B_153,A_154,C_155] :
      ( k1_xboole_0 = B_153
      | k1_relset_1(A_154,B_153,C_155) = A_154
      | ~ v1_funct_2(C_155,A_154,B_153)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(A_154,B_153))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_775,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_766])).

tff(c_786,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_539,c_775])).

tff(c_788,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_751,c_62,c_786])).

tff(c_789,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_750])).

tff(c_8,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_651,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k2_relat_1('#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_636])).

tff(c_656,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_651])).

tff(c_799,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_789,c_656])).

tff(c_819,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_559,c_799])).

tff(c_820,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_651])).

tff(c_12,plain,(
    ! [B_6,A_4] :
      ( v1_xboole_0(B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_4))
      | ~ v1_xboole_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_832,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_820,c_12])).

tff(c_839,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_832])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_843,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_839,c_4])).

tff(c_26,plain,(
    ! [B_18,C_19,A_17] :
      ( k1_xboole_0 = B_18
      | v1_funct_2(C_19,A_17,B_18)
      | k1_relset_1(A_17,B_18,C_19) != A_17
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1024,plain,(
    ! [B_170,C_171,A_172] :
      ( B_170 = '#skF_4'
      | v1_funct_2(C_171,A_172,B_170)
      | k1_relset_1(A_172,B_170,C_171) != A_172
      | ~ m1_subset_1(C_171,k1_zfmisc_1(k2_zfmisc_1(A_172,B_170))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_843,c_26])).

tff(c_1059,plain,(
    ! [B_177] :
      ( B_177 = '#skF_4'
      | v1_funct_2('#skF_4','#skF_1',B_177)
      | k1_relset_1('#skF_1',B_177,'#skF_4') != '#skF_1'
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_177) ) ),
    inference(resolution,[status(thm)],[c_619,c_1024])).

tff(c_1065,plain,
    ( '#skF_3' = '#skF_4'
    | v1_funct_2('#skF_4','#skF_1','#skF_3')
    | k1_relset_1('#skF_1','#skF_3','#skF_4') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_559,c_1059])).

tff(c_1070,plain,
    ( '#skF_3' = '#skF_4'
    | v1_funct_2('#skF_4','#skF_1','#skF_3')
    | k1_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1015,c_1065])).

tff(c_1071,plain,
    ( '#skF_3' = '#skF_4'
    | k1_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_528,c_1070])).

tff(c_1072,plain,(
    k1_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1071])).

tff(c_863,plain,(
    '#skF_2' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_843,c_62])).

tff(c_30,plain,(
    ! [B_18,A_17,C_19] :
      ( k1_xboole_0 = B_18
      | k1_relset_1(A_17,B_18,C_19) = A_17
      | ~ v1_funct_2(C_19,A_17,B_18)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1089,plain,(
    ! [B_184,A_185,C_186] :
      ( B_184 = '#skF_4'
      | k1_relset_1(A_185,B_184,C_186) = A_185
      | ~ v1_funct_2(C_186,A_185,B_184)
      | ~ m1_subset_1(C_186,k1_zfmisc_1(k2_zfmisc_1(A_185,B_184))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_843,c_30])).

tff(c_1101,plain,
    ( '#skF_2' = '#skF_4'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_1089])).

tff(c_1106,plain,
    ( '#skF_2' = '#skF_4'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_539,c_1101])).

tff(c_1108,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1072,c_863,c_1106])).

tff(c_1110,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1071])).

tff(c_10,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_535,plain,(
    ! [B_3,C_108] :
      ( k1_relset_1(k1_xboole_0,B_3,C_108) = k1_relat_1(C_108)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_529])).

tff(c_836,plain,(
    ! [B_3] : k1_relset_1(k1_xboole_0,B_3,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_820,c_535])).

tff(c_949,plain,(
    ! [B_3] : k1_relset_1('#skF_4',B_3,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_843,c_836])).

tff(c_448,plain,(
    ! [A_84,B_85,C_86] :
      ( k2_relset_1(A_84,B_85,C_86) = k2_relat_1(C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_458,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_448])).

tff(c_459,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_458,c_36])).

tff(c_483,plain,(
    ! [D_98,C_99,B_100,A_101] :
      ( m1_subset_1(D_98,k1_zfmisc_1(k2_zfmisc_1(C_99,B_100)))
      | ~ r1_tarski(k2_relat_1(D_98),B_100)
      | ~ m1_subset_1(D_98,k1_zfmisc_1(k2_zfmisc_1(C_99,A_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_493,plain,(
    ! [B_104] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_104)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_104) ) ),
    inference(resolution,[status(thm)],[c_38,c_483])).

tff(c_114,plain,(
    ! [A_34,B_35,C_36] :
      ( k2_relset_1(A_34,B_35,C_36) = k2_relat_1(C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_124,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_114])).

tff(c_125,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_36])).

tff(c_96,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_134,plain,(
    ! [D_45,C_46,B_47,A_48] :
      ( m1_subset_1(D_45,k1_zfmisc_1(k2_zfmisc_1(C_46,B_47)))
      | ~ r1_tarski(k2_relat_1(D_45),B_47)
      | ~ m1_subset_1(D_45,k1_zfmisc_1(k2_zfmisc_1(C_46,A_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_143,plain,(
    ! [B_49] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_49)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_49) ) ),
    inference(resolution,[status(thm)],[c_38,c_134])).

tff(c_174,plain,(
    ! [B_53] :
      ( k1_relset_1('#skF_1',B_53,'#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_53) ) ),
    inference(resolution,[status(thm)],[c_143,c_14])).

tff(c_178,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_125,c_174])).

tff(c_141,plain,(
    ! [B_47] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_47)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_47) ) ),
    inference(resolution,[status(thm)],[c_38,c_134])).

tff(c_216,plain,(
    ! [B_61,C_62,A_63] :
      ( k1_xboole_0 = B_61
      | v1_funct_2(C_62,A_63,B_61)
      | k1_relset_1(A_63,B_61,C_62) != A_63
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_252,plain,(
    ! [B_69] :
      ( k1_xboole_0 = B_69
      | v1_funct_2('#skF_4','#skF_1',B_69)
      | k1_relset_1('#skF_1',B_69,'#skF_4') != '#skF_1'
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_69) ) ),
    inference(resolution,[status(thm)],[c_141,c_216])).

tff(c_255,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4','#skF_1','#skF_3')
    | k1_relset_1('#skF_1','#skF_3','#skF_4') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_125,c_252])).

tff(c_257,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4','#skF_1','#skF_3')
    | k1_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_255])).

tff(c_258,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_257])).

tff(c_259,plain,(
    k1_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_258])).

tff(c_97,plain,(
    ! [A_27,B_28,C_29] :
      ( k1_relset_1(A_27,B_28,C_29) = k1_relat_1(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_107,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_97])).

tff(c_264,plain,(
    ! [B_73,A_74,C_75] :
      ( k1_xboole_0 = B_73
      | k1_relset_1(A_74,B_73,C_75) = A_74
      | ~ v1_funct_2(C_75,A_74,B_73)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_74,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_273,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_264])).

tff(c_284,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_107,c_273])).

tff(c_286,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_259,c_62,c_284])).

tff(c_287,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_258])).

tff(c_158,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k2_relat_1('#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_143])).

tff(c_163,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_158])).

tff(c_296,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_287,c_163])).

tff(c_312,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_296])).

tff(c_313,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_158])).

tff(c_328,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_313,c_12])).

tff(c_336,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_328])).

tff(c_340,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_336,c_4])).

tff(c_341,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_340,c_313])).

tff(c_20,plain,(
    ! [A_17] :
      ( v1_funct_2(k1_xboole_0,A_17,k1_xboole_0)
      | k1_xboole_0 = A_17
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_17,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_48,plain,(
    ! [A_17] :
      ( v1_funct_2(k1_xboole_0,A_17,k1_xboole_0)
      | k1_xboole_0 = A_17
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_20])).

tff(c_95,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_349,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_340,c_340,c_95])).

tff(c_445,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_341,c_349])).

tff(c_446,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_504,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_493,c_446])).

tff(c_518,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_459,c_504])).

tff(c_520,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_860,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_843,c_843,c_520])).

tff(c_24,plain,(
    ! [C_19,B_18] :
      ( v1_funct_2(C_19,k1_xboole_0,B_18)
      | k1_relset_1(k1_xboole_0,B_18,C_19) != k1_xboole_0
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_45,plain,(
    ! [C_19,B_18] :
      ( v1_funct_2(C_19,k1_xboole_0,B_18)
      | k1_relset_1(k1_xboole_0,B_18,C_19) != k1_xboole_0
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_24])).

tff(c_991,plain,(
    ! [C_166,B_167] :
      ( v1_funct_2(C_166,'#skF_4',B_167)
      | k1_relset_1('#skF_4',B_167,C_166) != '#skF_4'
      | ~ m1_subset_1(C_166,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_843,c_843,c_843,c_843,c_45])).

tff(c_993,plain,(
    ! [B_167] :
      ( v1_funct_2('#skF_4','#skF_4',B_167)
      | k1_relset_1('#skF_4',B_167,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_860,c_991])).

tff(c_995,plain,(
    ! [B_167] :
      ( v1_funct_2('#skF_4','#skF_4',B_167)
      | k1_relat_1('#skF_4') != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_949,c_993])).

tff(c_1022,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_995])).

tff(c_1122,plain,(
    '#skF_1' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1110,c_1022])).

tff(c_519,plain,(
    ! [A_17] :
      ( v1_funct_2(k1_xboole_0,A_17,k1_xboole_0)
      | k1_xboole_0 = A_17 ) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_859,plain,(
    ! [A_17] :
      ( v1_funct_2('#skF_4',A_17,'#skF_4')
      | A_17 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_843,c_843,c_843,c_519])).

tff(c_1109,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1071])).

tff(c_1114,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1109,c_528])).

tff(c_1137,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_859,c_1114])).

tff(c_1141,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1122,c_1137])).

tff(c_1142,plain,(
    ! [B_167] : v1_funct_2('#skF_4','#skF_4',B_167) ),
    inference(splitRight,[status(thm)],[c_995])).

tff(c_1143,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_995])).

tff(c_1148,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1143,c_539])).

tff(c_1248,plain,(
    ! [B_202,A_203,C_204] :
      ( B_202 = '#skF_4'
      | k1_relset_1(A_203,B_202,C_204) = A_203
      | ~ v1_funct_2(C_204,A_203,B_202)
      | ~ m1_subset_1(C_204,k1_zfmisc_1(k2_zfmisc_1(A_203,B_202))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_843,c_30])).

tff(c_1260,plain,
    ( '#skF_2' = '#skF_4'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_1248])).

tff(c_1265,plain,
    ( '#skF_2' = '#skF_4'
    | '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1148,c_1260])).

tff(c_1266,plain,(
    '#skF_1' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_863,c_1265])).

tff(c_1274,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1266,c_528])).

tff(c_1287,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1142,c_1274])).

tff(c_1288,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1382,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1371,c_1288])).

tff(c_1396,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1301,c_1382])).

tff(c_1397,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_1401,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1397,c_2])).

tff(c_1399,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1397,c_1397,c_8])).

tff(c_1398,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_1406,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1397,c_1398])).

tff(c_1442,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1399,c_1406,c_38])).

tff(c_1455,plain,(
    ! [B_230,A_231] :
      ( v1_xboole_0(B_230)
      | ~ m1_subset_1(B_230,k1_zfmisc_1(A_231))
      | ~ v1_xboole_0(A_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1458,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1442,c_1455])).

tff(c_1461,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1401,c_1458])).

tff(c_1400,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1397,c_4])).

tff(c_1465,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1461,c_1400])).

tff(c_1475,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1465,c_1397])).

tff(c_1672,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_1677,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1475,c_1475,c_1672])).

tff(c_1467,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1465,c_1442])).

tff(c_1678,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1677,c_1467])).

tff(c_1680,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1685,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1475,c_1475,c_1680])).

tff(c_1419,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_1',B_3) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1397,c_1397,c_10])).

tff(c_1470,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_4',B_3) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1465,c_1465,c_1419])).

tff(c_1560,plain,(
    ! [A_243,B_244,C_245] :
      ( k1_relset_1(A_243,B_244,C_245) = k1_relat_1(C_245)
      | ~ m1_subset_1(C_245,k1_zfmisc_1(k2_zfmisc_1(A_243,B_244))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1579,plain,(
    ! [B_249,C_250] :
      ( k1_relset_1('#skF_4',B_249,C_250) = k1_relat_1(C_250)
      | ~ m1_subset_1(C_250,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1470,c_1560])).

tff(c_1582,plain,(
    ! [B_249] : k1_relset_1('#skF_4',B_249,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1467,c_1579])).

tff(c_1407,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1406,c_40])).

tff(c_1472,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1465,c_1465,c_1407])).

tff(c_28,plain,(
    ! [B_18,C_19] :
      ( k1_relset_1(k1_xboole_0,B_18,C_19) = k1_xboole_0
      | ~ v1_funct_2(C_19,k1_xboole_0,B_18)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_46,plain,(
    ! [B_18,C_19] :
      ( k1_relset_1(k1_xboole_0,B_18,C_19) = k1_xboole_0
      | ~ v1_funct_2(C_19,k1_xboole_0,B_18)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_28])).

tff(c_1591,plain,(
    ! [B_252,C_253] :
      ( k1_relset_1('#skF_4',B_252,C_253) = '#skF_4'
      | ~ v1_funct_2(C_253,'#skF_4',B_252)
      | ~ m1_subset_1(C_253,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1475,c_1475,c_1475,c_1475,c_46])).

tff(c_1596,plain,
    ( k1_relset_1('#skF_4','#skF_4','#skF_4') = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1472,c_1591])).

tff(c_1603,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1467,c_1582,c_1596])).

tff(c_1604,plain,(
    ! [B_249] : k1_relset_1('#skF_4',B_249,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1603,c_1582])).

tff(c_1656,plain,(
    ! [C_261,B_262] :
      ( v1_funct_2(C_261,'#skF_4',B_262)
      | k1_relset_1('#skF_4',B_262,C_261) != '#skF_4'
      | ~ m1_subset_1(C_261,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1475,c_1475,c_1475,c_1475,c_45])).

tff(c_1658,plain,(
    ! [B_262] :
      ( v1_funct_2('#skF_4','#skF_4',B_262)
      | k1_relset_1('#skF_4',B_262,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_1467,c_1656])).

tff(c_1661,plain,(
    ! [B_262] : v1_funct_2('#skF_4','#skF_4',B_262) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1604,c_1658])).

tff(c_1481,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1465,c_1465,c_44])).

tff(c_1482,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1481])).

tff(c_1665,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1661,c_1482])).

tff(c_1666,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_1481])).

tff(c_1724,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1685,c_1470,c_1666])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:10:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.56/1.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.56/1.65  
% 3.56/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.56/1.66  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.56/1.66  
% 3.56/1.66  %Foreground sorts:
% 3.56/1.66  
% 3.56/1.66  
% 3.56/1.66  %Background operators:
% 3.56/1.66  
% 3.56/1.66  
% 3.56/1.66  %Foreground operators:
% 3.56/1.66  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.56/1.66  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.56/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.56/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.56/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.56/1.66  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.56/1.66  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.56/1.66  tff('#skF_2', type, '#skF_2': $i).
% 3.56/1.66  tff('#skF_3', type, '#skF_3': $i).
% 3.56/1.66  tff('#skF_1', type, '#skF_1': $i).
% 3.56/1.66  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.56/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.56/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.56/1.66  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.56/1.66  tff('#skF_4', type, '#skF_4': $i).
% 3.56/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.56/1.66  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.56/1.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.56/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.56/1.66  
% 3.56/1.68  tff(f_95, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(k2_relset_1(A, B, D), C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_2)).
% 3.56/1.68  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.56/1.68  tff(f_57, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_tarski(k2_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_relset_1)).
% 3.56/1.68  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.56/1.68  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.56/1.68  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.56/1.68  tff(f_36, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.56/1.68  tff(f_43, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 3.56/1.68  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.56/1.68  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.56/1.68  tff(c_1290, plain, (![A_205, B_206, C_207]: (k2_relset_1(A_205, B_206, C_207)=k2_relat_1(C_207) | ~m1_subset_1(C_207, k1_zfmisc_1(k2_zfmisc_1(A_205, B_206))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.56/1.68  tff(c_1300, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_1290])).
% 3.56/1.68  tff(c_36, plain, (r1_tarski(k2_relset_1('#skF_1', '#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.56/1.68  tff(c_1301, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1300, c_36])).
% 3.56/1.68  tff(c_1355, plain, (![D_219, C_220, B_221, A_222]: (m1_subset_1(D_219, k1_zfmisc_1(k2_zfmisc_1(C_220, B_221))) | ~r1_tarski(k2_relat_1(D_219), B_221) | ~m1_subset_1(D_219, k1_zfmisc_1(k2_zfmisc_1(C_220, A_222))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.56/1.68  tff(c_1371, plain, (![B_224]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_224))) | ~r1_tarski(k2_relat_1('#skF_4'), B_224))), inference(resolution, [status(thm)], [c_38, c_1355])).
% 3.56/1.68  tff(c_42, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.56/1.68  tff(c_32, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.56/1.68  tff(c_44, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_32])).
% 3.56/1.68  tff(c_528, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_44])).
% 3.56/1.68  tff(c_548, plain, (![A_111, B_112, C_113]: (k2_relset_1(A_111, B_112, C_113)=k2_relat_1(C_113) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.56/1.68  tff(c_558, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_548])).
% 3.56/1.68  tff(c_559, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_558, c_36])).
% 3.56/1.68  tff(c_612, plain, (![D_125, C_126, B_127, A_128]: (m1_subset_1(D_125, k1_zfmisc_1(k2_zfmisc_1(C_126, B_127))) | ~r1_tarski(k2_relat_1(D_125), B_127) | ~m1_subset_1(D_125, k1_zfmisc_1(k2_zfmisc_1(C_126, A_128))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.56/1.68  tff(c_636, plain, (![B_130]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_130))) | ~r1_tarski(k2_relat_1('#skF_4'), B_130))), inference(resolution, [status(thm)], [c_38, c_612])).
% 3.56/1.68  tff(c_14, plain, (![A_7, B_8, C_9]: (k1_relset_1(A_7, B_8, C_9)=k1_relat_1(C_9) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.56/1.68  tff(c_1006, plain, (![B_169]: (k1_relset_1('#skF_1', B_169, '#skF_4')=k1_relat_1('#skF_4') | ~r1_tarski(k2_relat_1('#skF_4'), B_169))), inference(resolution, [status(thm)], [c_636, c_14])).
% 3.56/1.68  tff(c_1015, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_559, c_1006])).
% 3.56/1.68  tff(c_619, plain, (![B_127]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_127))) | ~r1_tarski(k2_relat_1('#skF_4'), B_127))), inference(resolution, [status(thm)], [c_38, c_612])).
% 3.56/1.68  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.56/1.68  tff(c_674, plain, (![B_134]: (k1_relset_1('#skF_1', B_134, '#skF_4')=k1_relat_1('#skF_4') | ~r1_tarski(k2_relat_1('#skF_4'), B_134))), inference(resolution, [status(thm)], [c_636, c_14])).
% 3.56/1.68  tff(c_678, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_559, c_674])).
% 3.56/1.68  tff(c_695, plain, (![B_138, C_139, A_140]: (k1_xboole_0=B_138 | v1_funct_2(C_139, A_140, B_138) | k1_relset_1(A_140, B_138, C_139)!=A_140 | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(A_140, B_138))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.56/1.68  tff(c_744, plain, (![B_147]: (k1_xboole_0=B_147 | v1_funct_2('#skF_4', '#skF_1', B_147) | k1_relset_1('#skF_1', B_147, '#skF_4')!='#skF_1' | ~r1_tarski(k2_relat_1('#skF_4'), B_147))), inference(resolution, [status(thm)], [c_619, c_695])).
% 3.56/1.68  tff(c_747, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', '#skF_1', '#skF_3') | k1_relset_1('#skF_1', '#skF_3', '#skF_4')!='#skF_1'), inference(resolution, [status(thm)], [c_559, c_744])).
% 3.56/1.68  tff(c_749, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', '#skF_1', '#skF_3') | k1_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_678, c_747])).
% 3.56/1.68  tff(c_750, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_528, c_749])).
% 3.56/1.68  tff(c_751, plain, (k1_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_750])).
% 3.56/1.68  tff(c_34, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.56/1.68  tff(c_62, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_34])).
% 3.56/1.68  tff(c_40, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.56/1.68  tff(c_529, plain, (![A_106, B_107, C_108]: (k1_relset_1(A_106, B_107, C_108)=k1_relat_1(C_108) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.56/1.68  tff(c_539, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_529])).
% 3.56/1.68  tff(c_766, plain, (![B_153, A_154, C_155]: (k1_xboole_0=B_153 | k1_relset_1(A_154, B_153, C_155)=A_154 | ~v1_funct_2(C_155, A_154, B_153) | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(A_154, B_153))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.56/1.68  tff(c_775, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_766])).
% 3.56/1.68  tff(c_786, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_539, c_775])).
% 3.56/1.68  tff(c_788, plain, $false, inference(negUnitSimplification, [status(thm)], [c_751, c_62, c_786])).
% 3.56/1.68  tff(c_789, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_750])).
% 3.56/1.68  tff(c_8, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.56/1.68  tff(c_651, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1('#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_636])).
% 3.56/1.68  tff(c_656, plain, (~r1_tarski(k2_relat_1('#skF_4'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_651])).
% 3.56/1.68  tff(c_799, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_789, c_656])).
% 3.56/1.68  tff(c_819, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_559, c_799])).
% 3.56/1.68  tff(c_820, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_651])).
% 3.56/1.68  tff(c_12, plain, (![B_6, A_4]: (v1_xboole_0(B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_4)) | ~v1_xboole_0(A_4))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.56/1.68  tff(c_832, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_820, c_12])).
% 3.56/1.68  tff(c_839, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_832])).
% 3.56/1.68  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.56/1.68  tff(c_843, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_839, c_4])).
% 3.56/1.68  tff(c_26, plain, (![B_18, C_19, A_17]: (k1_xboole_0=B_18 | v1_funct_2(C_19, A_17, B_18) | k1_relset_1(A_17, B_18, C_19)!=A_17 | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.56/1.68  tff(c_1024, plain, (![B_170, C_171, A_172]: (B_170='#skF_4' | v1_funct_2(C_171, A_172, B_170) | k1_relset_1(A_172, B_170, C_171)!=A_172 | ~m1_subset_1(C_171, k1_zfmisc_1(k2_zfmisc_1(A_172, B_170))))), inference(demodulation, [status(thm), theory('equality')], [c_843, c_26])).
% 3.56/1.68  tff(c_1059, plain, (![B_177]: (B_177='#skF_4' | v1_funct_2('#skF_4', '#skF_1', B_177) | k1_relset_1('#skF_1', B_177, '#skF_4')!='#skF_1' | ~r1_tarski(k2_relat_1('#skF_4'), B_177))), inference(resolution, [status(thm)], [c_619, c_1024])).
% 3.56/1.68  tff(c_1065, plain, ('#skF_3'='#skF_4' | v1_funct_2('#skF_4', '#skF_1', '#skF_3') | k1_relset_1('#skF_1', '#skF_3', '#skF_4')!='#skF_1'), inference(resolution, [status(thm)], [c_559, c_1059])).
% 3.56/1.68  tff(c_1070, plain, ('#skF_3'='#skF_4' | v1_funct_2('#skF_4', '#skF_1', '#skF_3') | k1_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1015, c_1065])).
% 3.56/1.68  tff(c_1071, plain, ('#skF_3'='#skF_4' | k1_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_528, c_1070])).
% 3.56/1.68  tff(c_1072, plain, (k1_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_1071])).
% 3.56/1.68  tff(c_863, plain, ('#skF_2'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_843, c_62])).
% 3.56/1.68  tff(c_30, plain, (![B_18, A_17, C_19]: (k1_xboole_0=B_18 | k1_relset_1(A_17, B_18, C_19)=A_17 | ~v1_funct_2(C_19, A_17, B_18) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.56/1.68  tff(c_1089, plain, (![B_184, A_185, C_186]: (B_184='#skF_4' | k1_relset_1(A_185, B_184, C_186)=A_185 | ~v1_funct_2(C_186, A_185, B_184) | ~m1_subset_1(C_186, k1_zfmisc_1(k2_zfmisc_1(A_185, B_184))))), inference(demodulation, [status(thm), theory('equality')], [c_843, c_30])).
% 3.56/1.68  tff(c_1101, plain, ('#skF_2'='#skF_4' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_1089])).
% 3.56/1.68  tff(c_1106, plain, ('#skF_2'='#skF_4' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_539, c_1101])).
% 3.56/1.68  tff(c_1108, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1072, c_863, c_1106])).
% 3.56/1.68  tff(c_1110, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_1071])).
% 3.56/1.68  tff(c_10, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.56/1.68  tff(c_535, plain, (![B_3, C_108]: (k1_relset_1(k1_xboole_0, B_3, C_108)=k1_relat_1(C_108) | ~m1_subset_1(C_108, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_529])).
% 3.56/1.68  tff(c_836, plain, (![B_3]: (k1_relset_1(k1_xboole_0, B_3, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_820, c_535])).
% 3.56/1.68  tff(c_949, plain, (![B_3]: (k1_relset_1('#skF_4', B_3, '#skF_4')=k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_843, c_836])).
% 3.56/1.68  tff(c_448, plain, (![A_84, B_85, C_86]: (k2_relset_1(A_84, B_85, C_86)=k2_relat_1(C_86) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.56/1.68  tff(c_458, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_448])).
% 3.56/1.68  tff(c_459, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_458, c_36])).
% 3.56/1.68  tff(c_483, plain, (![D_98, C_99, B_100, A_101]: (m1_subset_1(D_98, k1_zfmisc_1(k2_zfmisc_1(C_99, B_100))) | ~r1_tarski(k2_relat_1(D_98), B_100) | ~m1_subset_1(D_98, k1_zfmisc_1(k2_zfmisc_1(C_99, A_101))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.56/1.68  tff(c_493, plain, (![B_104]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_104))) | ~r1_tarski(k2_relat_1('#skF_4'), B_104))), inference(resolution, [status(thm)], [c_38, c_483])).
% 3.56/1.68  tff(c_114, plain, (![A_34, B_35, C_36]: (k2_relset_1(A_34, B_35, C_36)=k2_relat_1(C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.56/1.68  tff(c_124, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_114])).
% 3.56/1.68  tff(c_125, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_36])).
% 3.56/1.68  tff(c_96, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_44])).
% 3.56/1.68  tff(c_134, plain, (![D_45, C_46, B_47, A_48]: (m1_subset_1(D_45, k1_zfmisc_1(k2_zfmisc_1(C_46, B_47))) | ~r1_tarski(k2_relat_1(D_45), B_47) | ~m1_subset_1(D_45, k1_zfmisc_1(k2_zfmisc_1(C_46, A_48))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.56/1.68  tff(c_143, plain, (![B_49]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_49))) | ~r1_tarski(k2_relat_1('#skF_4'), B_49))), inference(resolution, [status(thm)], [c_38, c_134])).
% 3.56/1.68  tff(c_174, plain, (![B_53]: (k1_relset_1('#skF_1', B_53, '#skF_4')=k1_relat_1('#skF_4') | ~r1_tarski(k2_relat_1('#skF_4'), B_53))), inference(resolution, [status(thm)], [c_143, c_14])).
% 3.56/1.68  tff(c_178, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_125, c_174])).
% 3.56/1.68  tff(c_141, plain, (![B_47]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_47))) | ~r1_tarski(k2_relat_1('#skF_4'), B_47))), inference(resolution, [status(thm)], [c_38, c_134])).
% 3.56/1.68  tff(c_216, plain, (![B_61, C_62, A_63]: (k1_xboole_0=B_61 | v1_funct_2(C_62, A_63, B_61) | k1_relset_1(A_63, B_61, C_62)!=A_63 | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_61))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.56/1.68  tff(c_252, plain, (![B_69]: (k1_xboole_0=B_69 | v1_funct_2('#skF_4', '#skF_1', B_69) | k1_relset_1('#skF_1', B_69, '#skF_4')!='#skF_1' | ~r1_tarski(k2_relat_1('#skF_4'), B_69))), inference(resolution, [status(thm)], [c_141, c_216])).
% 3.56/1.68  tff(c_255, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', '#skF_1', '#skF_3') | k1_relset_1('#skF_1', '#skF_3', '#skF_4')!='#skF_1'), inference(resolution, [status(thm)], [c_125, c_252])).
% 3.56/1.68  tff(c_257, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', '#skF_1', '#skF_3') | k1_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_178, c_255])).
% 3.56/1.68  tff(c_258, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_96, c_257])).
% 3.56/1.68  tff(c_259, plain, (k1_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_258])).
% 3.56/1.68  tff(c_97, plain, (![A_27, B_28, C_29]: (k1_relset_1(A_27, B_28, C_29)=k1_relat_1(C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.56/1.68  tff(c_107, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_97])).
% 3.56/1.68  tff(c_264, plain, (![B_73, A_74, C_75]: (k1_xboole_0=B_73 | k1_relset_1(A_74, B_73, C_75)=A_74 | ~v1_funct_2(C_75, A_74, B_73) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_74, B_73))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.56/1.68  tff(c_273, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_264])).
% 3.56/1.68  tff(c_284, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_107, c_273])).
% 3.56/1.68  tff(c_286, plain, $false, inference(negUnitSimplification, [status(thm)], [c_259, c_62, c_284])).
% 3.56/1.68  tff(c_287, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_258])).
% 3.56/1.68  tff(c_158, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1('#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_143])).
% 3.56/1.68  tff(c_163, plain, (~r1_tarski(k2_relat_1('#skF_4'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_158])).
% 3.56/1.68  tff(c_296, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_287, c_163])).
% 3.56/1.68  tff(c_312, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_125, c_296])).
% 3.56/1.68  tff(c_313, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_158])).
% 3.56/1.68  tff(c_328, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_313, c_12])).
% 3.56/1.68  tff(c_336, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_328])).
% 3.56/1.68  tff(c_340, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_336, c_4])).
% 3.56/1.68  tff(c_341, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_340, c_313])).
% 3.56/1.68  tff(c_20, plain, (![A_17]: (v1_funct_2(k1_xboole_0, A_17, k1_xboole_0) | k1_xboole_0=A_17 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_17, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.56/1.68  tff(c_48, plain, (![A_17]: (v1_funct_2(k1_xboole_0, A_17, k1_xboole_0) | k1_xboole_0=A_17 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_20])).
% 3.56/1.68  tff(c_95, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_48])).
% 3.56/1.68  tff(c_349, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_340, c_340, c_95])).
% 3.56/1.68  tff(c_445, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_341, c_349])).
% 3.56/1.68  tff(c_446, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(splitRight, [status(thm)], [c_44])).
% 3.56/1.68  tff(c_504, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_493, c_446])).
% 3.56/1.68  tff(c_518, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_459, c_504])).
% 3.56/1.68  tff(c_520, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_48])).
% 3.56/1.68  tff(c_860, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_843, c_843, c_520])).
% 3.56/1.68  tff(c_24, plain, (![C_19, B_18]: (v1_funct_2(C_19, k1_xboole_0, B_18) | k1_relset_1(k1_xboole_0, B_18, C_19)!=k1_xboole_0 | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_18))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.56/1.68  tff(c_45, plain, (![C_19, B_18]: (v1_funct_2(C_19, k1_xboole_0, B_18) | k1_relset_1(k1_xboole_0, B_18, C_19)!=k1_xboole_0 | ~m1_subset_1(C_19, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_24])).
% 3.56/1.68  tff(c_991, plain, (![C_166, B_167]: (v1_funct_2(C_166, '#skF_4', B_167) | k1_relset_1('#skF_4', B_167, C_166)!='#skF_4' | ~m1_subset_1(C_166, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_843, c_843, c_843, c_843, c_45])).
% 3.56/1.68  tff(c_993, plain, (![B_167]: (v1_funct_2('#skF_4', '#skF_4', B_167) | k1_relset_1('#skF_4', B_167, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_860, c_991])).
% 3.56/1.68  tff(c_995, plain, (![B_167]: (v1_funct_2('#skF_4', '#skF_4', B_167) | k1_relat_1('#skF_4')!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_949, c_993])).
% 3.56/1.68  tff(c_1022, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(splitLeft, [status(thm)], [c_995])).
% 3.56/1.68  tff(c_1122, plain, ('#skF_1'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1110, c_1022])).
% 3.56/1.68  tff(c_519, plain, (![A_17]: (v1_funct_2(k1_xboole_0, A_17, k1_xboole_0) | k1_xboole_0=A_17)), inference(splitRight, [status(thm)], [c_48])).
% 3.56/1.68  tff(c_859, plain, (![A_17]: (v1_funct_2('#skF_4', A_17, '#skF_4') | A_17='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_843, c_843, c_843, c_519])).
% 3.56/1.68  tff(c_1109, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_1071])).
% 3.56/1.68  tff(c_1114, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1109, c_528])).
% 3.56/1.68  tff(c_1137, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_859, c_1114])).
% 3.56/1.68  tff(c_1141, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1122, c_1137])).
% 3.56/1.68  tff(c_1142, plain, (![B_167]: (v1_funct_2('#skF_4', '#skF_4', B_167))), inference(splitRight, [status(thm)], [c_995])).
% 3.56/1.68  tff(c_1143, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_995])).
% 3.56/1.68  tff(c_1148, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1143, c_539])).
% 3.56/1.68  tff(c_1248, plain, (![B_202, A_203, C_204]: (B_202='#skF_4' | k1_relset_1(A_203, B_202, C_204)=A_203 | ~v1_funct_2(C_204, A_203, B_202) | ~m1_subset_1(C_204, k1_zfmisc_1(k2_zfmisc_1(A_203, B_202))))), inference(demodulation, [status(thm), theory('equality')], [c_843, c_30])).
% 3.56/1.68  tff(c_1260, plain, ('#skF_2'='#skF_4' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_1248])).
% 3.56/1.68  tff(c_1265, plain, ('#skF_2'='#skF_4' | '#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1148, c_1260])).
% 3.56/1.68  tff(c_1266, plain, ('#skF_1'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_863, c_1265])).
% 3.56/1.68  tff(c_1274, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1266, c_528])).
% 3.56/1.68  tff(c_1287, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1142, c_1274])).
% 3.56/1.68  tff(c_1288, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(splitRight, [status(thm)], [c_44])).
% 3.56/1.68  tff(c_1382, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_1371, c_1288])).
% 3.56/1.68  tff(c_1396, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1301, c_1382])).
% 3.56/1.68  tff(c_1397, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_34])).
% 3.56/1.68  tff(c_1401, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1397, c_2])).
% 3.56/1.68  tff(c_1399, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1397, c_1397, c_8])).
% 3.56/1.68  tff(c_1398, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_34])).
% 3.56/1.68  tff(c_1406, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1397, c_1398])).
% 3.56/1.68  tff(c_1442, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1399, c_1406, c_38])).
% 3.56/1.68  tff(c_1455, plain, (![B_230, A_231]: (v1_xboole_0(B_230) | ~m1_subset_1(B_230, k1_zfmisc_1(A_231)) | ~v1_xboole_0(A_231))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.56/1.68  tff(c_1458, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_1442, c_1455])).
% 3.56/1.68  tff(c_1461, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1401, c_1458])).
% 3.56/1.68  tff(c_1400, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_1397, c_4])).
% 3.56/1.68  tff(c_1465, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_1461, c_1400])).
% 3.56/1.68  tff(c_1475, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1465, c_1397])).
% 3.56/1.68  tff(c_1672, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_48])).
% 3.56/1.68  tff(c_1677, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1475, c_1475, c_1672])).
% 3.56/1.68  tff(c_1467, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1465, c_1442])).
% 3.56/1.68  tff(c_1678, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1677, c_1467])).
% 3.56/1.68  tff(c_1680, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_48])).
% 3.56/1.68  tff(c_1685, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1475, c_1475, c_1680])).
% 3.56/1.68  tff(c_1419, plain, (![B_3]: (k2_zfmisc_1('#skF_1', B_3)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1397, c_1397, c_10])).
% 3.56/1.68  tff(c_1470, plain, (![B_3]: (k2_zfmisc_1('#skF_4', B_3)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1465, c_1465, c_1419])).
% 3.56/1.68  tff(c_1560, plain, (![A_243, B_244, C_245]: (k1_relset_1(A_243, B_244, C_245)=k1_relat_1(C_245) | ~m1_subset_1(C_245, k1_zfmisc_1(k2_zfmisc_1(A_243, B_244))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.56/1.68  tff(c_1579, plain, (![B_249, C_250]: (k1_relset_1('#skF_4', B_249, C_250)=k1_relat_1(C_250) | ~m1_subset_1(C_250, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_1470, c_1560])).
% 3.56/1.68  tff(c_1582, plain, (![B_249]: (k1_relset_1('#skF_4', B_249, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_1467, c_1579])).
% 3.56/1.68  tff(c_1407, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1406, c_40])).
% 3.56/1.68  tff(c_1472, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1465, c_1465, c_1407])).
% 3.56/1.68  tff(c_28, plain, (![B_18, C_19]: (k1_relset_1(k1_xboole_0, B_18, C_19)=k1_xboole_0 | ~v1_funct_2(C_19, k1_xboole_0, B_18) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_18))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.56/1.68  tff(c_46, plain, (![B_18, C_19]: (k1_relset_1(k1_xboole_0, B_18, C_19)=k1_xboole_0 | ~v1_funct_2(C_19, k1_xboole_0, B_18) | ~m1_subset_1(C_19, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_28])).
% 3.56/1.68  tff(c_1591, plain, (![B_252, C_253]: (k1_relset_1('#skF_4', B_252, C_253)='#skF_4' | ~v1_funct_2(C_253, '#skF_4', B_252) | ~m1_subset_1(C_253, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1475, c_1475, c_1475, c_1475, c_46])).
% 3.56/1.68  tff(c_1596, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_4')='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_1472, c_1591])).
% 3.56/1.68  tff(c_1603, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1467, c_1582, c_1596])).
% 3.56/1.68  tff(c_1604, plain, (![B_249]: (k1_relset_1('#skF_4', B_249, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1603, c_1582])).
% 3.56/1.68  tff(c_1656, plain, (![C_261, B_262]: (v1_funct_2(C_261, '#skF_4', B_262) | k1_relset_1('#skF_4', B_262, C_261)!='#skF_4' | ~m1_subset_1(C_261, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1475, c_1475, c_1475, c_1475, c_45])).
% 3.56/1.68  tff(c_1658, plain, (![B_262]: (v1_funct_2('#skF_4', '#skF_4', B_262) | k1_relset_1('#skF_4', B_262, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_1467, c_1656])).
% 3.56/1.68  tff(c_1661, plain, (![B_262]: (v1_funct_2('#skF_4', '#skF_4', B_262))), inference(demodulation, [status(thm), theory('equality')], [c_1604, c_1658])).
% 3.56/1.68  tff(c_1481, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1465, c_1465, c_44])).
% 3.56/1.68  tff(c_1482, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_1481])).
% 3.56/1.68  tff(c_1665, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1661, c_1482])).
% 3.56/1.68  tff(c_1666, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_1481])).
% 3.56/1.68  tff(c_1724, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1685, c_1470, c_1666])).
% 3.56/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.56/1.68  
% 3.56/1.68  Inference rules
% 3.56/1.68  ----------------------
% 3.56/1.68  #Ref     : 0
% 3.56/1.68  #Sup     : 372
% 3.56/1.68  #Fact    : 0
% 3.56/1.68  #Define  : 0
% 3.56/1.68  #Split   : 18
% 3.56/1.68  #Chain   : 0
% 3.56/1.68  #Close   : 0
% 3.56/1.68  
% 3.56/1.68  Ordering : KBO
% 3.56/1.68  
% 3.56/1.68  Simplification rules
% 3.56/1.68  ----------------------
% 3.56/1.68  #Subsume      : 18
% 3.56/1.68  #Demod        : 388
% 3.56/1.68  #Tautology    : 236
% 3.56/1.68  #SimpNegUnit  : 14
% 3.56/1.68  #BackRed      : 127
% 3.56/1.68  
% 3.56/1.68  #Partial instantiations: 0
% 3.56/1.68  #Strategies tried      : 1
% 3.56/1.68  
% 3.56/1.68  Timing (in seconds)
% 3.56/1.68  ----------------------
% 3.83/1.69  Preprocessing        : 0.34
% 3.83/1.69  Parsing              : 0.18
% 3.83/1.69  CNF conversion       : 0.02
% 3.83/1.69  Main loop            : 0.49
% 3.83/1.69  Inferencing          : 0.17
% 3.83/1.69  Reduction            : 0.16
% 3.83/1.69  Demodulation         : 0.11
% 3.83/1.69  BG Simplification    : 0.03
% 3.83/1.69  Subsumption          : 0.08
% 3.83/1.69  Abstraction          : 0.02
% 3.83/1.69  MUC search           : 0.00
% 3.83/1.69  Cooper               : 0.00
% 3.83/1.69  Total                : 0.89
% 3.83/1.69  Index Insertion      : 0.00
% 3.83/1.69  Index Deletion       : 0.00
% 3.83/1.69  Index Matching       : 0.00
% 3.83/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
