%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:22 EST 2020

% Result     : Theorem 48.92s
% Output     : CNFRefutation 49.27s
% Verified   : 
% Statistics : Number of formulae       :  254 (4349 expanded)
%              Number of leaves         :   39 (1491 expanded)
%              Depth                    :   22
%              Number of atoms          :  477 (13394 expanded)
%              Number of equality atoms :  165 (4526 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_129,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ~ ( r2_hidden(F,A)
                    & r2_hidden(F,C)
                    & E = k1_funct_1(D,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_funct_2)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_47,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
      <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_110,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_60,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_59474,plain,(
    ! [A_2382,B_2383,C_2384,D_2385] :
      ( k7_relset_1(A_2382,B_2383,C_2384,D_2385) = k9_relat_1(C_2384,D_2385)
      | ~ m1_subset_1(C_2384,k1_zfmisc_1(k2_zfmisc_1(A_2382,B_2383))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_59481,plain,(
    ! [D_2385] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_2385) = k9_relat_1('#skF_8',D_2385) ),
    inference(resolution,[status(thm)],[c_60,c_59474])).

tff(c_58,plain,(
    r2_hidden('#skF_9',k7_relset_1('#skF_5','#skF_6','#skF_8','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_59487,plain,(
    r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59481,c_58])).

tff(c_16,plain,(
    ! [A_12,B_13] : v1_relat_1(k2_zfmisc_1(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_78,plain,(
    ! [B_62,A_63] :
      ( v1_relat_1(B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_63))
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_84,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_60,c_78])).

tff(c_88,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_84])).

tff(c_181,plain,(
    ! [A_84,B_85,C_86] :
      ( k1_relset_1(A_84,B_85,C_86) = k1_relat_1(C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_190,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_60,c_181])).

tff(c_152158,plain,(
    ! [A_5128,B_5129,C_5130] :
      ( r2_hidden('#skF_3'(A_5128,B_5129,C_5130),B_5129)
      | k1_relset_1(B_5129,A_5128,C_5130) = B_5129
      | ~ m1_subset_1(C_5130,k1_zfmisc_1(k2_zfmisc_1(B_5129,A_5128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_152163,plain,
    ( r2_hidden('#skF_3'('#skF_6','#skF_5','#skF_8'),'#skF_5')
    | k1_relset_1('#skF_5','#skF_6','#skF_8') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_60,c_152158])).

tff(c_152166,plain,
    ( r2_hidden('#skF_3'('#skF_6','#skF_5','#skF_8'),'#skF_5')
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_152163])).

tff(c_152167,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_152166])).

tff(c_24,plain,(
    ! [A_14,B_15,C_16] :
      ( r2_hidden('#skF_2'(A_14,B_15,C_16),k1_relat_1(C_16))
      | ~ r2_hidden(A_14,k9_relat_1(C_16,B_15))
      | ~ v1_relat_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_152172,plain,(
    ! [A_14,B_15] :
      ( r2_hidden('#skF_2'(A_14,B_15,'#skF_8'),'#skF_5')
      | ~ r2_hidden(A_14,k9_relat_1('#skF_8',B_15))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_152167,c_24])).

tff(c_152211,plain,(
    ! [A_5134,B_5135] :
      ( r2_hidden('#skF_2'(A_5134,B_5135,'#skF_8'),'#skF_5')
      | ~ r2_hidden(A_5134,k9_relat_1('#skF_8',B_5135)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_152172])).

tff(c_242,plain,(
    ! [A_97,B_98,C_99] :
      ( r2_hidden('#skF_2'(A_97,B_98,C_99),B_98)
      | ~ r2_hidden(A_97,k9_relat_1(C_99,B_98))
      | ~ v1_relat_1(C_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_56,plain,(
    ! [F_53] :
      ( k1_funct_1('#skF_8',F_53) != '#skF_9'
      | ~ r2_hidden(F_53,'#skF_7')
      | ~ r2_hidden(F_53,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_250,plain,(
    ! [A_97,C_99] :
      ( k1_funct_1('#skF_8','#skF_2'(A_97,'#skF_7',C_99)) != '#skF_9'
      | ~ r2_hidden('#skF_2'(A_97,'#skF_7',C_99),'#skF_5')
      | ~ r2_hidden(A_97,k9_relat_1(C_99,'#skF_7'))
      | ~ v1_relat_1(C_99) ) ),
    inference(resolution,[status(thm)],[c_242,c_56])).

tff(c_152215,plain,(
    ! [A_5134] :
      ( k1_funct_1('#skF_8','#skF_2'(A_5134,'#skF_7','#skF_8')) != '#skF_9'
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(A_5134,k9_relat_1('#skF_8','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_152211,c_250])).

tff(c_152235,plain,(
    ! [A_5138] :
      ( k1_funct_1('#skF_8','#skF_2'(A_5138,'#skF_7','#skF_8')) != '#skF_9'
      | ~ r2_hidden(A_5138,k9_relat_1('#skF_8','#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_152215])).

tff(c_152276,plain,(
    k1_funct_1('#skF_8','#skF_2'('#skF_9','#skF_7','#skF_8')) != '#skF_9' ),
    inference(resolution,[status(thm)],[c_59487,c_152235])).

tff(c_64,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_59575,plain,(
    ! [A_2408,B_2409,C_2410] :
      ( r2_hidden(k4_tarski('#skF_2'(A_2408,B_2409,C_2410),A_2408),C_2410)
      | ~ r2_hidden(A_2408,k9_relat_1(C_2410,B_2409))
      | ~ v1_relat_1(C_2410) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_28,plain,(
    ! [C_22,A_20,B_21] :
      ( k1_funct_1(C_22,A_20) = B_21
      | ~ r2_hidden(k4_tarski(A_20,B_21),C_22)
      | ~ v1_funct_1(C_22)
      | ~ v1_relat_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_152345,plain,(
    ! [C_5151,A_5152,B_5153] :
      ( k1_funct_1(C_5151,'#skF_2'(A_5152,B_5153,C_5151)) = A_5152
      | ~ v1_funct_1(C_5151)
      | ~ r2_hidden(A_5152,k9_relat_1(C_5151,B_5153))
      | ~ v1_relat_1(C_5151) ) ),
    inference(resolution,[status(thm)],[c_59575,c_28])).

tff(c_152368,plain,
    ( k1_funct_1('#skF_8','#skF_2'('#skF_9','#skF_7','#skF_8')) = '#skF_9'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_59487,c_152345])).

tff(c_152387,plain,(
    k1_funct_1('#skF_8','#skF_2'('#skF_9','#skF_7','#skF_8')) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_152368])).

tff(c_152389,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_152276,c_152387])).

tff(c_152391,plain,(
    k1_relat_1('#skF_8') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_152166])).

tff(c_62,plain,(
    v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_153788,plain,(
    ! [B_5288,A_5289,C_5290] :
      ( k1_xboole_0 = B_5288
      | k1_relset_1(A_5289,B_5288,C_5290) = A_5289
      | ~ v1_funct_2(C_5290,A_5289,B_5288)
      | ~ m1_subset_1(C_5290,k1_zfmisc_1(k2_zfmisc_1(A_5289,B_5288))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_153795,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_153788])).

tff(c_153799,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_190,c_153795])).

tff(c_153800,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_152391,c_153799])).

tff(c_131,plain,(
    ! [A_74,B_75] :
      ( r2_hidden('#skF_1'(A_74,B_75),A_74)
      | r1_tarski(A_74,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_140,plain,(
    ! [A_74] : r1_tarski(A_74,A_74) ),
    inference(resolution,[status(thm)],[c_131,c_4])).

tff(c_67,plain,(
    ! [A_57,B_58] :
      ( r1_tarski(A_57,B_58)
      | ~ m1_subset_1(A_57,k1_zfmisc_1(B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_71,plain,(
    r1_tarski('#skF_8',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_60,c_67])).

tff(c_152493,plain,(
    ! [B_5163,A_5164,C_5165] :
      ( k1_xboole_0 = B_5163
      | k1_relset_1(A_5164,B_5163,C_5165) = A_5164
      | ~ v1_funct_2(C_5165,A_5164,B_5163)
      | ~ m1_subset_1(C_5165,k1_zfmisc_1(k2_zfmisc_1(A_5164,B_5163))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_152500,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_152493])).

tff(c_152504,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_190,c_152500])).

tff(c_152505,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_152391,c_152504])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_253,plain,(
    ! [C_106,A_107] :
      ( k1_xboole_0 = C_106
      | ~ v1_funct_2(C_106,A_107,k1_xboole_0)
      | k1_xboole_0 = A_107
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_107,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_258,plain,(
    ! [A_7,A_107] :
      ( k1_xboole_0 = A_7
      | ~ v1_funct_2(A_7,A_107,k1_xboole_0)
      | k1_xboole_0 = A_107
      | ~ r1_tarski(A_7,k2_zfmisc_1(A_107,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_12,c_253])).

tff(c_152827,plain,(
    ! [A_5201,A_5202] :
      ( A_5201 = '#skF_6'
      | ~ v1_funct_2(A_5201,A_5202,'#skF_6')
      | A_5202 = '#skF_6'
      | ~ r1_tarski(A_5201,k2_zfmisc_1(A_5202,'#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152505,c_152505,c_152505,c_152505,c_258])).

tff(c_152841,plain,
    ( '#skF_6' = '#skF_8'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6')
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_71,c_152827])).

tff(c_152848,plain,
    ( '#skF_6' = '#skF_8'
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_152841])).

tff(c_152849,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_152848])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_152390,plain,(
    r2_hidden('#skF_3'('#skF_6','#skF_5','#skF_8'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_152166])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_152395,plain,(
    ! [B_5154] :
      ( r2_hidden('#skF_3'('#skF_6','#skF_5','#skF_8'),B_5154)
      | ~ r1_tarski('#skF_5',B_5154) ) ),
    inference(resolution,[status(thm)],[c_152390,c_2])).

tff(c_152411,plain,(
    ! [B_5155,B_5156] :
      ( r2_hidden('#skF_3'('#skF_6','#skF_5','#skF_8'),B_5155)
      | ~ r1_tarski(B_5156,B_5155)
      | ~ r1_tarski('#skF_5',B_5156) ) ),
    inference(resolution,[status(thm)],[c_152395,c_2])).

tff(c_152431,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_3'('#skF_6','#skF_5','#skF_8'),A_6)
      | ~ r1_tarski('#skF_5',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_152411])).

tff(c_152452,plain,(
    ~ r1_tarski('#skF_5',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_152431])).

tff(c_152508,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_152505,c_152452])).

tff(c_152851,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_152849,c_152508])).

tff(c_152887,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_152851])).

tff(c_152888,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_152848])).

tff(c_152529,plain,(
    ! [A_6] : r1_tarski('#skF_6',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152505,c_8])).

tff(c_152906,plain,(
    ! [A_6] : r1_tarski('#skF_8',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152888,c_152529])).

tff(c_59869,plain,(
    ! [C_2452,A_2453,B_2454] :
      ( k1_funct_1(C_2452,'#skF_2'(A_2453,B_2454,C_2452)) = A_2453
      | ~ v1_funct_1(C_2452)
      | ~ r2_hidden(A_2453,k9_relat_1(C_2452,B_2454))
      | ~ v1_relat_1(C_2452) ) ),
    inference(resolution,[status(thm)],[c_59575,c_28])).

tff(c_59883,plain,
    ( k1_funct_1('#skF_8','#skF_2'('#skF_9','#skF_7','#skF_8')) = '#skF_9'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_59487,c_59869])).

tff(c_59899,plain,(
    k1_funct_1('#skF_8','#skF_2'('#skF_9','#skF_7','#skF_8')) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_59883])).

tff(c_59912,plain,(
    ! [B_2455,A_2456,C_2457] :
      ( k1_xboole_0 = B_2455
      | k1_relset_1(A_2456,B_2455,C_2457) = A_2456
      | ~ v1_funct_2(C_2457,A_2456,B_2455)
      | ~ m1_subset_1(C_2457,k1_zfmisc_1(k2_zfmisc_1(A_2456,B_2455))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_59919,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_59912])).

tff(c_59923,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_190,c_59919])).

tff(c_59924,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_59923])).

tff(c_59929,plain,(
    ! [A_14,B_15] :
      ( r2_hidden('#skF_2'(A_14,B_15,'#skF_8'),'#skF_5')
      | ~ r2_hidden(A_14,k9_relat_1('#skF_8',B_15))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59924,c_24])).

tff(c_59952,plain,(
    ! [A_2461,B_2462] :
      ( r2_hidden('#skF_2'(A_2461,B_2462,'#skF_8'),'#skF_5')
      | ~ r2_hidden(A_2461,k9_relat_1('#skF_8',B_2462)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_59929])).

tff(c_59959,plain,(
    ! [A_2461] :
      ( k1_funct_1('#skF_8','#skF_2'(A_2461,'#skF_7','#skF_8')) != '#skF_9'
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(A_2461,k9_relat_1('#skF_8','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_59952,c_250])).

tff(c_59969,plain,(
    ! [A_2463] :
      ( k1_funct_1('#skF_8','#skF_2'(A_2463,'#skF_7','#skF_8')) != '#skF_9'
      | ~ r2_hidden(A_2463,k9_relat_1('#skF_8','#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_59959])).

tff(c_59988,plain,(
    k1_funct_1('#skF_8','#skF_2'('#skF_9','#skF_7','#skF_8')) != '#skF_9' ),
    inference(resolution,[status(thm)],[c_59487,c_59969])).

tff(c_60008,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_59899,c_59988])).

tff(c_60010,plain,(
    k1_relat_1('#skF_8') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_59923])).

tff(c_60009,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_59923])).

tff(c_150137,plain,(
    ! [A_4931,A_4932] :
      ( A_4931 = '#skF_6'
      | ~ v1_funct_2(A_4931,A_4932,'#skF_6')
      | A_4932 = '#skF_6'
      | ~ r1_tarski(A_4931,k2_zfmisc_1(A_4932,'#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60009,c_60009,c_60009,c_60009,c_258])).

tff(c_150155,plain,
    ( '#skF_6' = '#skF_8'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6')
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_71,c_150137])).

tff(c_150163,plain,
    ( '#skF_6' = '#skF_8'
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_150155])).

tff(c_150164,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_150163])).

tff(c_150177,plain,(
    k1_relat_1('#skF_8') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_150164,c_60010])).

tff(c_150199,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_150164,c_62])).

tff(c_150195,plain,(
    k1_relset_1('#skF_6','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_150164,c_190])).

tff(c_150197,plain,(
    r1_tarski('#skF_8',k2_zfmisc_1('#skF_6','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_150164,c_71])).

tff(c_59822,plain,(
    ! [B_2442,C_2443] :
      ( k1_relset_1(k1_xboole_0,B_2442,C_2443) = k1_xboole_0
      | ~ v1_funct_2(C_2443,k1_xboole_0,B_2442)
      | ~ m1_subset_1(C_2443,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_2442))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_59827,plain,(
    ! [B_2442,A_7] :
      ( k1_relset_1(k1_xboole_0,B_2442,A_7) = k1_xboole_0
      | ~ v1_funct_2(A_7,k1_xboole_0,B_2442)
      | ~ r1_tarski(A_7,k2_zfmisc_1(k1_xboole_0,B_2442)) ) ),
    inference(resolution,[status(thm)],[c_12,c_59822])).

tff(c_150364,plain,(
    ! [B_4938,A_4939] :
      ( k1_relset_1('#skF_6',B_4938,A_4939) = '#skF_6'
      | ~ v1_funct_2(A_4939,'#skF_6',B_4938)
      | ~ r1_tarski(A_4939,k2_zfmisc_1('#skF_6',B_4938)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60009,c_60009,c_60009,c_60009,c_59827])).

tff(c_150367,plain,
    ( k1_relset_1('#skF_6','#skF_6','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_150197,c_150364])).

tff(c_150378,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_150199,c_150195,c_150367])).

tff(c_150380,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_150177,c_150378])).

tff(c_150381,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_150163])).

tff(c_150407,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_150381,c_60])).

tff(c_203,plain,(
    ! [A_89,B_90,A_91] :
      ( k1_relset_1(A_89,B_90,A_91) = k1_relat_1(A_91)
      | ~ r1_tarski(A_91,k2_zfmisc_1(A_89,B_90)) ) ),
    inference(resolution,[status(thm)],[c_12,c_181])).

tff(c_218,plain,(
    ! [A_89,B_90] : k1_relset_1(A_89,B_90,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_203])).

tff(c_60025,plain,(
    ! [A_89,B_90] : k1_relset_1(A_89,B_90,'#skF_6') = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60009,c_60009,c_218])).

tff(c_150391,plain,(
    ! [A_89,B_90] : k1_relset_1(A_89,B_90,'#skF_8') = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_150381,c_150381,c_60025])).

tff(c_60389,plain,(
    ! [A_2505,A_2506] :
      ( A_2505 = '#skF_6'
      | ~ v1_funct_2(A_2505,A_2506,'#skF_6')
      | A_2506 = '#skF_6'
      | ~ r1_tarski(A_2505,k2_zfmisc_1(A_2506,'#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60009,c_60009,c_60009,c_60009,c_258])).

tff(c_60403,plain,
    ( '#skF_6' = '#skF_8'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6')
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_71,c_60389])).

tff(c_60410,plain,
    ( '#skF_6' = '#skF_8'
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60403])).

tff(c_60411,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_60410])).

tff(c_60028,plain,(
    ! [A_6] : r1_tarski('#skF_6',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60009,c_8])).

tff(c_60129,plain,(
    ! [A_2477,B_2478,C_2479] :
      ( r2_hidden('#skF_3'(A_2477,B_2478,C_2479),B_2478)
      | k1_relset_1(B_2478,A_2477,C_2479) = B_2478
      | ~ m1_subset_1(C_2479,k1_zfmisc_1(k2_zfmisc_1(B_2478,A_2477))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_60134,plain,
    ( r2_hidden('#skF_3'('#skF_6','#skF_5','#skF_8'),'#skF_5')
    | k1_relset_1('#skF_5','#skF_6','#skF_8') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_60,c_60129])).

tff(c_60137,plain,
    ( r2_hidden('#skF_3'('#skF_6','#skF_5','#skF_8'),'#skF_5')
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_60134])).

tff(c_60138,plain,(
    r2_hidden('#skF_3'('#skF_6','#skF_5','#skF_8'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_60010,c_60137])).

tff(c_60195,plain,(
    ! [B_2486] :
      ( r2_hidden('#skF_3'('#skF_6','#skF_5','#skF_8'),B_2486)
      | ~ r1_tarski('#skF_5',B_2486) ) ),
    inference(resolution,[status(thm)],[c_60138,c_2])).

tff(c_60234,plain,(
    ! [B_2494,B_2495] :
      ( r2_hidden('#skF_3'('#skF_6','#skF_5','#skF_8'),B_2494)
      | ~ r1_tarski(B_2495,B_2494)
      | ~ r1_tarski('#skF_5',B_2495) ) ),
    inference(resolution,[status(thm)],[c_60195,c_2])).

tff(c_60247,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_3'('#skF_6','#skF_5','#skF_8'),A_6)
      | ~ r1_tarski('#skF_5','#skF_6') ) ),
    inference(resolution,[status(thm)],[c_60028,c_60234])).

tff(c_60265,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_60247])).

tff(c_60414,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60411,c_60265])).

tff(c_60450,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_60414])).

tff(c_60451,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_60410])).

tff(c_59761,plain,(
    ! [C_2432,B_2433] :
      ( v1_funct_2(C_2432,k1_xboole_0,B_2433)
      | k1_relset_1(k1_xboole_0,B_2433,C_2432) != k1_xboole_0
      | ~ m1_subset_1(C_2432,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_2433))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_59781,plain,(
    ! [A_2436,B_2437] :
      ( v1_funct_2(A_2436,k1_xboole_0,B_2437)
      | k1_relset_1(k1_xboole_0,B_2437,A_2436) != k1_xboole_0
      | ~ r1_tarski(A_2436,k2_zfmisc_1(k1_xboole_0,B_2437)) ) ),
    inference(resolution,[status(thm)],[c_12,c_59761])).

tff(c_59789,plain,(
    ! [B_2437] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_2437)
      | k1_relset_1(k1_xboole_0,B_2437,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_59781])).

tff(c_59793,plain,(
    ! [B_2437] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_2437)
      | k1_relat_1(k1_xboole_0) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_59789])).

tff(c_59794,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_59793])).

tff(c_60017,plain,(
    k1_relat_1('#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60009,c_60009,c_59794])).

tff(c_60471,plain,(
    k1_relat_1('#skF_8') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60451,c_60451,c_60017])).

tff(c_60468,plain,(
    ! [A_89,B_90] : k1_relset_1(A_89,B_90,'#skF_8') = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60451,c_60451,c_60025])).

tff(c_60472,plain,(
    ! [A_6] : r1_tarski('#skF_8',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60451,c_60028])).

tff(c_61102,plain,(
    ! [A_2561,B_2562,A_2563] :
      ( r2_hidden('#skF_3'(A_2561,B_2562,A_2563),B_2562)
      | k1_relset_1(B_2562,A_2561,A_2563) = B_2562
      | ~ r1_tarski(A_2563,k2_zfmisc_1(B_2562,A_2561)) ) ),
    inference(resolution,[status(thm)],[c_12,c_60129])).

tff(c_61839,plain,(
    ! [A_2650,B_2651,A_2652,B_2653] :
      ( r2_hidden('#skF_3'(A_2650,B_2651,A_2652),B_2653)
      | ~ r1_tarski(B_2651,B_2653)
      | k1_relset_1(B_2651,A_2650,A_2652) = B_2651
      | ~ r1_tarski(A_2652,k2_zfmisc_1(B_2651,A_2650)) ) ),
    inference(resolution,[status(thm)],[c_61102,c_2])).

tff(c_26,plain,(
    ! [A_20,C_22] :
      ( r2_hidden(k4_tarski(A_20,k1_funct_1(C_22,A_20)),C_22)
      | ~ r2_hidden(A_20,k1_relat_1(C_22))
      | ~ v1_funct_1(C_22)
      | ~ v1_relat_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_60221,plain,(
    ! [A_2489,B_2490,C_2491,E_2492] :
      ( ~ r2_hidden(k4_tarski('#skF_3'(A_2489,B_2490,C_2491),E_2492),C_2491)
      | k1_relset_1(B_2490,A_2489,C_2491) = B_2490
      | ~ m1_subset_1(C_2491,k1_zfmisc_1(k2_zfmisc_1(B_2490,A_2489))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_60226,plain,(
    ! [B_2490,A_2489,C_22] :
      ( k1_relset_1(B_2490,A_2489,C_22) = B_2490
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(B_2490,A_2489)))
      | ~ r2_hidden('#skF_3'(A_2489,B_2490,C_22),k1_relat_1(C_22))
      | ~ v1_funct_1(C_22)
      | ~ v1_relat_1(C_22) ) ),
    inference(resolution,[status(thm)],[c_26,c_60221])).

tff(c_120358,plain,(
    ! [A_4417,B_4418,A_4419] :
      ( ~ m1_subset_1(A_4417,k1_zfmisc_1(k2_zfmisc_1(B_4418,A_4419)))
      | ~ v1_funct_1(A_4417)
      | ~ v1_relat_1(A_4417)
      | ~ r1_tarski(B_4418,k1_relat_1(A_4417))
      | k1_relset_1(B_4418,A_4419,A_4417) = B_4418
      | ~ r1_tarski(A_4417,k2_zfmisc_1(B_4418,A_4419)) ) ),
    inference(resolution,[status(thm)],[c_61839,c_60226])).

tff(c_149359,plain,(
    ! [A_4883,B_4884,A_4885] :
      ( ~ v1_funct_1(A_4883)
      | ~ v1_relat_1(A_4883)
      | ~ r1_tarski(B_4884,k1_relat_1(A_4883))
      | k1_relset_1(B_4884,A_4885,A_4883) = B_4884
      | ~ r1_tarski(A_4883,k2_zfmisc_1(B_4884,A_4885)) ) ),
    inference(resolution,[status(thm)],[c_12,c_120358])).

tff(c_149414,plain,(
    ! [A_4888,A_4889] :
      ( ~ v1_funct_1(A_4888)
      | ~ v1_relat_1(A_4888)
      | k1_relset_1('#skF_8',A_4889,A_4888) = '#skF_8'
      | ~ r1_tarski(A_4888,k2_zfmisc_1('#skF_8',A_4889)) ) ),
    inference(resolution,[status(thm)],[c_60472,c_149359])).

tff(c_149446,plain,(
    ! [A_4889] :
      ( ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | k1_relset_1('#skF_8',A_4889,'#skF_8') = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_60472,c_149414])).

tff(c_149460,plain,(
    k1_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60468,c_88,c_64,c_149446])).

tff(c_149462,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60471,c_149460])).

tff(c_149464,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_60247])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_153,plain,(
    ! [C_77,B_78,A_79] :
      ( r2_hidden(C_77,B_78)
      | ~ r2_hidden(C_77,A_79)
      | ~ r1_tarski(A_79,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_167,plain,(
    ! [A_81,B_82,B_83] :
      ( r2_hidden('#skF_1'(A_81,B_82),B_83)
      | ~ r1_tarski(A_81,B_83)
      | r1_tarski(A_81,B_82) ) ),
    inference(resolution,[status(thm)],[c_6,c_153])).

tff(c_59538,plain,(
    ! [A_2401,B_2402,B_2403,B_2404] :
      ( r2_hidden('#skF_1'(A_2401,B_2402),B_2403)
      | ~ r1_tarski(B_2404,B_2403)
      | ~ r1_tarski(A_2401,B_2404)
      | r1_tarski(A_2401,B_2402) ) ),
    inference(resolution,[status(thm)],[c_167,c_2])).

tff(c_59551,plain,(
    ! [A_2405,B_2406,A_2407] :
      ( r2_hidden('#skF_1'(A_2405,B_2406),A_2407)
      | ~ r1_tarski(A_2405,k1_xboole_0)
      | r1_tarski(A_2405,B_2406) ) ),
    inference(resolution,[status(thm)],[c_8,c_59538])).

tff(c_59573,plain,(
    ! [A_2405,A_2407] :
      ( ~ r1_tarski(A_2405,k1_xboole_0)
      | r1_tarski(A_2405,A_2407) ) ),
    inference(resolution,[status(thm)],[c_59551,c_4])).

tff(c_60020,plain,(
    ! [A_2405,A_2407] :
      ( ~ r1_tarski(A_2405,'#skF_6')
      | r1_tarski(A_2405,A_2407) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60009,c_59573])).

tff(c_149479,plain,(
    ! [A_2407] : r1_tarski('#skF_5',A_2407) ),
    inference(resolution,[status(thm)],[c_149464,c_60020])).

tff(c_60254,plain,
    ( r2_hidden('#skF_3'('#skF_6','#skF_5','#skF_8'),k2_zfmisc_1('#skF_5','#skF_6'))
    | ~ r1_tarski('#skF_5','#skF_8') ),
    inference(resolution,[status(thm)],[c_71,c_60234])).

tff(c_60255,plain,(
    ~ r1_tarski('#skF_5','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_60254])).

tff(c_149496,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_149479,c_60255])).

tff(c_149498,plain,(
    r1_tarski('#skF_5','#skF_8') ),
    inference(splitRight,[status(thm)],[c_60254])).

tff(c_149770,plain,(
    ! [A_4910,A_4911] :
      ( A_4910 = '#skF_6'
      | ~ v1_funct_2(A_4910,A_4911,'#skF_6')
      | A_4911 = '#skF_6'
      | ~ r1_tarski(A_4910,k2_zfmisc_1(A_4911,'#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60009,c_60009,c_60009,c_60009,c_258])).

tff(c_149784,plain,
    ( '#skF_6' = '#skF_8'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6')
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_71,c_149770])).

tff(c_149791,plain,
    ( '#skF_6' = '#skF_8'
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_149784])).

tff(c_149792,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_149791])).

tff(c_149639,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_60247])).

tff(c_149800,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_149792,c_149639])).

tff(c_149841,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60028,c_149800])).

tff(c_149842,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_149791])).

tff(c_149848,plain,(
    ~ r1_tarski('#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_149842,c_149639])).

tff(c_149883,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_149498,c_149848])).

tff(c_149884,plain,(
    ! [A_6] : r2_hidden('#skF_3'('#skF_6','#skF_5','#skF_8'),A_6) ),
    inference(splitRight,[status(thm)],[c_60247])).

tff(c_150384,plain,(
    ! [A_6] : r2_hidden('#skF_3'('#skF_8','#skF_5','#skF_8'),A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_150381,c_149884])).

tff(c_151956,plain,(
    ! [B_5098,A_5099,C_5100] :
      ( k1_relset_1(B_5098,A_5099,C_5100) = B_5098
      | ~ m1_subset_1(C_5100,k1_zfmisc_1(k2_zfmisc_1(B_5098,A_5099)))
      | ~ r2_hidden('#skF_3'(A_5099,B_5098,C_5100),k1_relat_1(C_5100))
      | ~ v1_funct_1(C_5100)
      | ~ v1_relat_1(C_5100) ) ),
    inference(resolution,[status(thm)],[c_26,c_60221])).

tff(c_151968,plain,
    ( k1_relset_1('#skF_5','#skF_8','#skF_8') = '#skF_5'
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_8')))
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_150384,c_151956])).

tff(c_151973,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_150407,c_150391,c_151968])).

tff(c_151975,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60010,c_151973])).

tff(c_151977,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_59793])).

tff(c_152519,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_152505,c_152505,c_151977])).

tff(c_152904,plain,(
    k1_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_152888,c_152888,c_152519])).

tff(c_152940,plain,(
    ! [A_14,B_15] :
      ( r2_hidden('#skF_2'(A_14,B_15,'#skF_8'),'#skF_8')
      | ~ r2_hidden(A_14,k9_relat_1('#skF_8',B_15))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_152904,c_24])).

tff(c_153163,plain,(
    ! [A_5229,B_5230] :
      ( r2_hidden('#skF_2'(A_5229,B_5230,'#skF_8'),'#skF_8')
      | ~ r2_hidden(A_5229,k9_relat_1('#skF_8',B_5230)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_152940])).

tff(c_153167,plain,(
    ! [A_5229,B_5230,B_2] :
      ( r2_hidden('#skF_2'(A_5229,B_5230,'#skF_8'),B_2)
      | ~ r1_tarski('#skF_8',B_2)
      | ~ r2_hidden(A_5229,k9_relat_1('#skF_8',B_5230)) ) ),
    inference(resolution,[status(thm)],[c_153163,c_2])).

tff(c_153172,plain,(
    ! [A_5231,B_5232,B_5233] :
      ( r2_hidden('#skF_2'(A_5231,B_5232,'#skF_8'),B_5233)
      | ~ r2_hidden(A_5231,k9_relat_1('#skF_8',B_5232)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152906,c_153167])).

tff(c_153178,plain,(
    ! [A_5231] :
      ( k1_funct_1('#skF_8','#skF_2'(A_5231,'#skF_7','#skF_8')) != '#skF_9'
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(A_5231,k9_relat_1('#skF_8','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_153172,c_250])).

tff(c_153264,plain,(
    ! [A_5244] :
      ( k1_funct_1('#skF_8','#skF_2'(A_5244,'#skF_7','#skF_8')) != '#skF_9'
      | ~ r2_hidden(A_5244,k9_relat_1('#skF_8','#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_153178])).

tff(c_153315,plain,(
    k1_funct_1('#skF_8','#skF_2'('#skF_9','#skF_7','#skF_8')) != '#skF_9' ),
    inference(resolution,[status(thm)],[c_59487,c_153264])).

tff(c_153576,plain,(
    ! [C_5283,A_5284,B_5285] :
      ( k1_funct_1(C_5283,'#skF_2'(A_5284,B_5285,C_5283)) = A_5284
      | ~ v1_funct_1(C_5283)
      | ~ r2_hidden(A_5284,k9_relat_1(C_5283,B_5285))
      | ~ v1_relat_1(C_5283) ) ),
    inference(resolution,[status(thm)],[c_59575,c_28])).

tff(c_153607,plain,
    ( k1_funct_1('#skF_8','#skF_2'('#skF_9','#skF_7','#skF_8')) = '#skF_9'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_59487,c_153576])).

tff(c_153629,plain,(
    k1_funct_1('#skF_8','#skF_2'('#skF_9','#skF_7','#skF_8')) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_153607])).

tff(c_153631,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_153315,c_153629])).

tff(c_153633,plain,(
    r1_tarski('#skF_5',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_152431])).

tff(c_153706,plain,(
    ! [A_5286] : r1_tarski('#skF_5',A_5286) ),
    inference(resolution,[status(thm)],[c_153633,c_59573])).

tff(c_153763,plain,(
    ! [A_107] :
      ( k1_xboole_0 = '#skF_5'
      | ~ v1_funct_2('#skF_5',A_107,k1_xboole_0)
      | k1_xboole_0 = A_107 ) ),
    inference(resolution,[status(thm)],[c_153706,c_258])).

tff(c_154025,plain,(
    ! [A_107] :
      ( '#skF_5' = '#skF_6'
      | ~ v1_funct_2('#skF_5',A_107,'#skF_6')
      | A_107 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_153800,c_153800,c_153800,c_153763])).

tff(c_154026,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_154025])).

tff(c_154034,plain,(
    k1_relat_1('#skF_8') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_154026,c_152391])).

tff(c_154056,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154026,c_62])).

tff(c_154052,plain,(
    k1_relset_1('#skF_6','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154026,c_190])).

tff(c_154054,plain,(
    r1_tarski('#skF_8',k2_zfmisc_1('#skF_6','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154026,c_71])).

tff(c_152081,plain,(
    ! [B_5114,C_5115] :
      ( k1_relset_1(k1_xboole_0,B_5114,C_5115) = k1_xboole_0
      | ~ v1_funct_2(C_5115,k1_xboole_0,B_5114)
      | ~ m1_subset_1(C_5115,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_5114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_152086,plain,(
    ! [B_5114,A_7] :
      ( k1_relset_1(k1_xboole_0,B_5114,A_7) = k1_xboole_0
      | ~ v1_funct_2(A_7,k1_xboole_0,B_5114)
      | ~ r1_tarski(A_7,k2_zfmisc_1(k1_xboole_0,B_5114)) ) ),
    inference(resolution,[status(thm)],[c_12,c_152081])).

tff(c_154339,plain,(
    ! [B_5342,A_5343] :
      ( k1_relset_1('#skF_6',B_5342,A_5343) = '#skF_6'
      | ~ v1_funct_2(A_5343,'#skF_6',B_5342)
      | ~ r1_tarski(A_5343,k2_zfmisc_1('#skF_6',B_5342)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_153800,c_153800,c_153800,c_153800,c_152086])).

tff(c_154345,plain,
    ( k1_relset_1('#skF_6','#skF_6','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_154054,c_154339])).

tff(c_154357,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_154056,c_154052,c_154345])).

tff(c_154359,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_154034,c_154357])).

tff(c_154361,plain,(
    '#skF_5' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_154025])).

tff(c_154515,plain,(
    ! [A_5365,A_5366] :
      ( A_5365 = '#skF_6'
      | ~ v1_funct_2(A_5365,A_5366,'#skF_6')
      | A_5366 = '#skF_6'
      | ~ r1_tarski(A_5365,k2_zfmisc_1(A_5366,'#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_153800,c_153800,c_153800,c_153800,c_258])).

tff(c_154533,plain,
    ( '#skF_6' = '#skF_8'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6')
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_71,c_154515])).

tff(c_154544,plain,
    ( '#skF_6' = '#skF_8'
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_154533])).

tff(c_154545,plain,(
    '#skF_6' = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_154361,c_154544])).

tff(c_153822,plain,(
    ! [A_6] : r1_tarski('#skF_6',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_153800,c_8])).

tff(c_154562,plain,(
    ! [A_6] : r1_tarski('#skF_8',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154545,c_153822])).

tff(c_153812,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_153800,c_153800,c_151977])).

tff(c_154561,plain,(
    k1_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_154545,c_154545,c_153812])).

tff(c_154630,plain,(
    ! [A_14,B_15] :
      ( r2_hidden('#skF_2'(A_14,B_15,'#skF_8'),'#skF_8')
      | ~ r2_hidden(A_14,k9_relat_1('#skF_8',B_15))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_154561,c_24])).

tff(c_154854,plain,(
    ! [A_5394,B_5395] :
      ( r2_hidden('#skF_2'(A_5394,B_5395,'#skF_8'),'#skF_8')
      | ~ r2_hidden(A_5394,k9_relat_1('#skF_8',B_5395)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_154630])).

tff(c_154858,plain,(
    ! [A_5394,B_5395,B_2] :
      ( r2_hidden('#skF_2'(A_5394,B_5395,'#skF_8'),B_2)
      | ~ r1_tarski('#skF_8',B_2)
      | ~ r2_hidden(A_5394,k9_relat_1('#skF_8',B_5395)) ) ),
    inference(resolution,[status(thm)],[c_154854,c_2])).

tff(c_154865,plain,(
    ! [A_5396,B_5397,B_5398] :
      ( r2_hidden('#skF_2'(A_5396,B_5397,'#skF_8'),B_5398)
      | ~ r2_hidden(A_5396,k9_relat_1('#skF_8',B_5397)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154562,c_154858])).

tff(c_154871,plain,(
    ! [A_5396] :
      ( k1_funct_1('#skF_8','#skF_2'(A_5396,'#skF_7','#skF_8')) != '#skF_9'
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(A_5396,k9_relat_1('#skF_8','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_154865,c_250])).

tff(c_154975,plain,(
    ! [A_5411] :
      ( k1_funct_1('#skF_8','#skF_2'(A_5411,'#skF_7','#skF_8')) != '#skF_9'
      | ~ r2_hidden(A_5411,k9_relat_1('#skF_8','#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_154871])).

tff(c_155016,plain,(
    k1_funct_1('#skF_8','#skF_2'('#skF_9','#skF_7','#skF_8')) != '#skF_9' ),
    inference(resolution,[status(thm)],[c_59487,c_154975])).

tff(c_155195,plain,(
    ! [C_5441,A_5442,B_5443] :
      ( k1_funct_1(C_5441,'#skF_2'(A_5442,B_5443,C_5441)) = A_5442
      | ~ v1_funct_1(C_5441)
      | ~ r2_hidden(A_5442,k9_relat_1(C_5441,B_5443))
      | ~ v1_relat_1(C_5441) ) ),
    inference(resolution,[status(thm)],[c_59575,c_28])).

tff(c_155219,plain,
    ( k1_funct_1('#skF_8','#skF_2'('#skF_9','#skF_7','#skF_8')) = '#skF_9'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_59487,c_155195])).

tff(c_155239,plain,(
    k1_funct_1('#skF_8','#skF_2'('#skF_9','#skF_7','#skF_8')) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_155219])).

tff(c_155241,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_155016,c_155239])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:09:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 48.92/37.93  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 49.09/37.96  
% 49.09/37.96  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 49.09/37.96  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3 > #skF_1
% 49.09/37.96  
% 49.09/37.96  %Foreground sorts:
% 49.09/37.96  
% 49.09/37.96  
% 49.09/37.96  %Background operators:
% 49.09/37.96  
% 49.09/37.96  
% 49.09/37.96  %Foreground operators:
% 49.09/37.96  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 49.09/37.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 49.09/37.96  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 49.09/37.96  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 49.09/37.96  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 49.09/37.96  tff('#skF_7', type, '#skF_7': $i).
% 49.09/37.96  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 49.09/37.96  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 49.09/37.96  tff('#skF_5', type, '#skF_5': $i).
% 49.09/37.96  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 49.09/37.96  tff('#skF_6', type, '#skF_6': $i).
% 49.09/37.96  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 49.09/37.96  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 49.09/37.96  tff('#skF_9', type, '#skF_9': $i).
% 49.09/37.96  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 49.09/37.96  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 49.09/37.96  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 49.09/37.96  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 49.09/37.96  tff('#skF_8', type, '#skF_8': $i).
% 49.09/37.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 49.09/37.96  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 49.09/37.96  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 49.09/37.96  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 49.09/37.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 49.09/37.96  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 49.09/37.96  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 49.09/37.96  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 49.09/37.96  
% 49.27/37.99  tff(f_129, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t115_funct_2)).
% 49.27/37.99  tff(f_80, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 49.27/37.99  tff(f_47, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 49.27/37.99  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 49.27/37.99  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 49.27/37.99  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relset_1)).
% 49.27/37.99  tff(f_58, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 49.27/37.99  tff(f_68, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 49.27/37.99  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 49.27/37.99  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 49.27/37.99  tff(f_38, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 49.27/37.99  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 49.27/37.99  tff(c_60, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_129])).
% 49.27/37.99  tff(c_59474, plain, (![A_2382, B_2383, C_2384, D_2385]: (k7_relset_1(A_2382, B_2383, C_2384, D_2385)=k9_relat_1(C_2384, D_2385) | ~m1_subset_1(C_2384, k1_zfmisc_1(k2_zfmisc_1(A_2382, B_2383))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 49.27/37.99  tff(c_59481, plain, (![D_2385]: (k7_relset_1('#skF_5', '#skF_6', '#skF_8', D_2385)=k9_relat_1('#skF_8', D_2385))), inference(resolution, [status(thm)], [c_60, c_59474])).
% 49.27/37.99  tff(c_58, plain, (r2_hidden('#skF_9', k7_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_129])).
% 49.27/37.99  tff(c_59487, plain, (r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_59481, c_58])).
% 49.27/37.99  tff(c_16, plain, (![A_12, B_13]: (v1_relat_1(k2_zfmisc_1(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 49.27/37.99  tff(c_78, plain, (![B_62, A_63]: (v1_relat_1(B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(A_63)) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_45])).
% 49.27/37.99  tff(c_84, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_60, c_78])).
% 49.27/37.99  tff(c_88, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_84])).
% 49.27/37.99  tff(c_181, plain, (![A_84, B_85, C_86]: (k1_relset_1(A_84, B_85, C_86)=k1_relat_1(C_86) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 49.27/37.99  tff(c_190, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_60, c_181])).
% 49.27/37.99  tff(c_152158, plain, (![A_5128, B_5129, C_5130]: (r2_hidden('#skF_3'(A_5128, B_5129, C_5130), B_5129) | k1_relset_1(B_5129, A_5128, C_5130)=B_5129 | ~m1_subset_1(C_5130, k1_zfmisc_1(k2_zfmisc_1(B_5129, A_5128))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 49.27/37.99  tff(c_152163, plain, (r2_hidden('#skF_3'('#skF_6', '#skF_5', '#skF_8'), '#skF_5') | k1_relset_1('#skF_5', '#skF_6', '#skF_8')='#skF_5'), inference(resolution, [status(thm)], [c_60, c_152158])).
% 49.27/37.99  tff(c_152166, plain, (r2_hidden('#skF_3'('#skF_6', '#skF_5', '#skF_8'), '#skF_5') | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_190, c_152163])).
% 49.27/37.99  tff(c_152167, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(splitLeft, [status(thm)], [c_152166])).
% 49.27/37.99  tff(c_24, plain, (![A_14, B_15, C_16]: (r2_hidden('#skF_2'(A_14, B_15, C_16), k1_relat_1(C_16)) | ~r2_hidden(A_14, k9_relat_1(C_16, B_15)) | ~v1_relat_1(C_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 49.27/37.99  tff(c_152172, plain, (![A_14, B_15]: (r2_hidden('#skF_2'(A_14, B_15, '#skF_8'), '#skF_5') | ~r2_hidden(A_14, k9_relat_1('#skF_8', B_15)) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_152167, c_24])).
% 49.27/37.99  tff(c_152211, plain, (![A_5134, B_5135]: (r2_hidden('#skF_2'(A_5134, B_5135, '#skF_8'), '#skF_5') | ~r2_hidden(A_5134, k9_relat_1('#skF_8', B_5135)))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_152172])).
% 49.27/37.99  tff(c_242, plain, (![A_97, B_98, C_99]: (r2_hidden('#skF_2'(A_97, B_98, C_99), B_98) | ~r2_hidden(A_97, k9_relat_1(C_99, B_98)) | ~v1_relat_1(C_99))), inference(cnfTransformation, [status(thm)], [f_58])).
% 49.27/37.99  tff(c_56, plain, (![F_53]: (k1_funct_1('#skF_8', F_53)!='#skF_9' | ~r2_hidden(F_53, '#skF_7') | ~r2_hidden(F_53, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_129])).
% 49.27/37.99  tff(c_250, plain, (![A_97, C_99]: (k1_funct_1('#skF_8', '#skF_2'(A_97, '#skF_7', C_99))!='#skF_9' | ~r2_hidden('#skF_2'(A_97, '#skF_7', C_99), '#skF_5') | ~r2_hidden(A_97, k9_relat_1(C_99, '#skF_7')) | ~v1_relat_1(C_99))), inference(resolution, [status(thm)], [c_242, c_56])).
% 49.27/37.99  tff(c_152215, plain, (![A_5134]: (k1_funct_1('#skF_8', '#skF_2'(A_5134, '#skF_7', '#skF_8'))!='#skF_9' | ~v1_relat_1('#skF_8') | ~r2_hidden(A_5134, k9_relat_1('#skF_8', '#skF_7')))), inference(resolution, [status(thm)], [c_152211, c_250])).
% 49.27/37.99  tff(c_152235, plain, (![A_5138]: (k1_funct_1('#skF_8', '#skF_2'(A_5138, '#skF_7', '#skF_8'))!='#skF_9' | ~r2_hidden(A_5138, k9_relat_1('#skF_8', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_152215])).
% 49.27/37.99  tff(c_152276, plain, (k1_funct_1('#skF_8', '#skF_2'('#skF_9', '#skF_7', '#skF_8'))!='#skF_9'), inference(resolution, [status(thm)], [c_59487, c_152235])).
% 49.27/37.99  tff(c_64, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_129])).
% 49.27/37.99  tff(c_59575, plain, (![A_2408, B_2409, C_2410]: (r2_hidden(k4_tarski('#skF_2'(A_2408, B_2409, C_2410), A_2408), C_2410) | ~r2_hidden(A_2408, k9_relat_1(C_2410, B_2409)) | ~v1_relat_1(C_2410))), inference(cnfTransformation, [status(thm)], [f_58])).
% 49.27/37.99  tff(c_28, plain, (![C_22, A_20, B_21]: (k1_funct_1(C_22, A_20)=B_21 | ~r2_hidden(k4_tarski(A_20, B_21), C_22) | ~v1_funct_1(C_22) | ~v1_relat_1(C_22))), inference(cnfTransformation, [status(thm)], [f_68])).
% 49.27/37.99  tff(c_152345, plain, (![C_5151, A_5152, B_5153]: (k1_funct_1(C_5151, '#skF_2'(A_5152, B_5153, C_5151))=A_5152 | ~v1_funct_1(C_5151) | ~r2_hidden(A_5152, k9_relat_1(C_5151, B_5153)) | ~v1_relat_1(C_5151))), inference(resolution, [status(thm)], [c_59575, c_28])).
% 49.27/37.99  tff(c_152368, plain, (k1_funct_1('#skF_8', '#skF_2'('#skF_9', '#skF_7', '#skF_8'))='#skF_9' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_59487, c_152345])).
% 49.27/37.99  tff(c_152387, plain, (k1_funct_1('#skF_8', '#skF_2'('#skF_9', '#skF_7', '#skF_8'))='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_152368])).
% 49.27/37.99  tff(c_152389, plain, $false, inference(negUnitSimplification, [status(thm)], [c_152276, c_152387])).
% 49.27/37.99  tff(c_152391, plain, (k1_relat_1('#skF_8')!='#skF_5'), inference(splitRight, [status(thm)], [c_152166])).
% 49.27/37.99  tff(c_62, plain, (v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_129])).
% 49.27/37.99  tff(c_153788, plain, (![B_5288, A_5289, C_5290]: (k1_xboole_0=B_5288 | k1_relset_1(A_5289, B_5288, C_5290)=A_5289 | ~v1_funct_2(C_5290, A_5289, B_5288) | ~m1_subset_1(C_5290, k1_zfmisc_1(k2_zfmisc_1(A_5289, B_5288))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 49.27/37.99  tff(c_153795, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_60, c_153788])).
% 49.27/37.99  tff(c_153799, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_190, c_153795])).
% 49.27/37.99  tff(c_153800, plain, (k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_152391, c_153799])).
% 49.27/37.99  tff(c_131, plain, (![A_74, B_75]: (r2_hidden('#skF_1'(A_74, B_75), A_74) | r1_tarski(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_32])).
% 49.27/37.99  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 49.27/37.99  tff(c_140, plain, (![A_74]: (r1_tarski(A_74, A_74))), inference(resolution, [status(thm)], [c_131, c_4])).
% 49.27/37.99  tff(c_67, plain, (![A_57, B_58]: (r1_tarski(A_57, B_58) | ~m1_subset_1(A_57, k1_zfmisc_1(B_58)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 49.27/37.99  tff(c_71, plain, (r1_tarski('#skF_8', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_60, c_67])).
% 49.27/37.99  tff(c_152493, plain, (![B_5163, A_5164, C_5165]: (k1_xboole_0=B_5163 | k1_relset_1(A_5164, B_5163, C_5165)=A_5164 | ~v1_funct_2(C_5165, A_5164, B_5163) | ~m1_subset_1(C_5165, k1_zfmisc_1(k2_zfmisc_1(A_5164, B_5163))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 49.27/37.99  tff(c_152500, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_60, c_152493])).
% 49.27/37.99  tff(c_152504, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_190, c_152500])).
% 49.27/37.99  tff(c_152505, plain, (k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_152391, c_152504])).
% 49.27/37.99  tff(c_12, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 49.27/37.99  tff(c_253, plain, (![C_106, A_107]: (k1_xboole_0=C_106 | ~v1_funct_2(C_106, A_107, k1_xboole_0) | k1_xboole_0=A_107 | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_107, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 49.27/37.99  tff(c_258, plain, (![A_7, A_107]: (k1_xboole_0=A_7 | ~v1_funct_2(A_7, A_107, k1_xboole_0) | k1_xboole_0=A_107 | ~r1_tarski(A_7, k2_zfmisc_1(A_107, k1_xboole_0)))), inference(resolution, [status(thm)], [c_12, c_253])).
% 49.27/37.99  tff(c_152827, plain, (![A_5201, A_5202]: (A_5201='#skF_6' | ~v1_funct_2(A_5201, A_5202, '#skF_6') | A_5202='#skF_6' | ~r1_tarski(A_5201, k2_zfmisc_1(A_5202, '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_152505, c_152505, c_152505, c_152505, c_258])).
% 49.27/37.99  tff(c_152841, plain, ('#skF_6'='#skF_8' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6') | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_71, c_152827])).
% 49.27/37.99  tff(c_152848, plain, ('#skF_6'='#skF_8' | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_152841])).
% 49.27/37.99  tff(c_152849, plain, ('#skF_5'='#skF_6'), inference(splitLeft, [status(thm)], [c_152848])).
% 49.27/37.99  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 49.27/37.99  tff(c_152390, plain, (r2_hidden('#skF_3'('#skF_6', '#skF_5', '#skF_8'), '#skF_5')), inference(splitRight, [status(thm)], [c_152166])).
% 49.27/37.99  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 49.27/37.99  tff(c_152395, plain, (![B_5154]: (r2_hidden('#skF_3'('#skF_6', '#skF_5', '#skF_8'), B_5154) | ~r1_tarski('#skF_5', B_5154))), inference(resolution, [status(thm)], [c_152390, c_2])).
% 49.27/37.99  tff(c_152411, plain, (![B_5155, B_5156]: (r2_hidden('#skF_3'('#skF_6', '#skF_5', '#skF_8'), B_5155) | ~r1_tarski(B_5156, B_5155) | ~r1_tarski('#skF_5', B_5156))), inference(resolution, [status(thm)], [c_152395, c_2])).
% 49.27/37.99  tff(c_152431, plain, (![A_6]: (r2_hidden('#skF_3'('#skF_6', '#skF_5', '#skF_8'), A_6) | ~r1_tarski('#skF_5', k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_152411])).
% 49.27/37.99  tff(c_152452, plain, (~r1_tarski('#skF_5', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_152431])).
% 49.27/37.99  tff(c_152508, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_152505, c_152452])).
% 49.27/37.99  tff(c_152851, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_152849, c_152508])).
% 49.27/37.99  tff(c_152887, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_140, c_152851])).
% 49.27/37.99  tff(c_152888, plain, ('#skF_6'='#skF_8'), inference(splitRight, [status(thm)], [c_152848])).
% 49.27/37.99  tff(c_152529, plain, (![A_6]: (r1_tarski('#skF_6', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_152505, c_8])).
% 49.27/37.99  tff(c_152906, plain, (![A_6]: (r1_tarski('#skF_8', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_152888, c_152529])).
% 49.27/37.99  tff(c_59869, plain, (![C_2452, A_2453, B_2454]: (k1_funct_1(C_2452, '#skF_2'(A_2453, B_2454, C_2452))=A_2453 | ~v1_funct_1(C_2452) | ~r2_hidden(A_2453, k9_relat_1(C_2452, B_2454)) | ~v1_relat_1(C_2452))), inference(resolution, [status(thm)], [c_59575, c_28])).
% 49.27/37.99  tff(c_59883, plain, (k1_funct_1('#skF_8', '#skF_2'('#skF_9', '#skF_7', '#skF_8'))='#skF_9' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_59487, c_59869])).
% 49.27/37.99  tff(c_59899, plain, (k1_funct_1('#skF_8', '#skF_2'('#skF_9', '#skF_7', '#skF_8'))='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_59883])).
% 49.27/37.99  tff(c_59912, plain, (![B_2455, A_2456, C_2457]: (k1_xboole_0=B_2455 | k1_relset_1(A_2456, B_2455, C_2457)=A_2456 | ~v1_funct_2(C_2457, A_2456, B_2455) | ~m1_subset_1(C_2457, k1_zfmisc_1(k2_zfmisc_1(A_2456, B_2455))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 49.27/37.99  tff(c_59919, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_60, c_59912])).
% 49.27/37.99  tff(c_59923, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_190, c_59919])).
% 49.27/37.99  tff(c_59924, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(splitLeft, [status(thm)], [c_59923])).
% 49.27/37.99  tff(c_59929, plain, (![A_14, B_15]: (r2_hidden('#skF_2'(A_14, B_15, '#skF_8'), '#skF_5') | ~r2_hidden(A_14, k9_relat_1('#skF_8', B_15)) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_59924, c_24])).
% 49.27/37.99  tff(c_59952, plain, (![A_2461, B_2462]: (r2_hidden('#skF_2'(A_2461, B_2462, '#skF_8'), '#skF_5') | ~r2_hidden(A_2461, k9_relat_1('#skF_8', B_2462)))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_59929])).
% 49.27/37.99  tff(c_59959, plain, (![A_2461]: (k1_funct_1('#skF_8', '#skF_2'(A_2461, '#skF_7', '#skF_8'))!='#skF_9' | ~v1_relat_1('#skF_8') | ~r2_hidden(A_2461, k9_relat_1('#skF_8', '#skF_7')))), inference(resolution, [status(thm)], [c_59952, c_250])).
% 49.27/37.99  tff(c_59969, plain, (![A_2463]: (k1_funct_1('#skF_8', '#skF_2'(A_2463, '#skF_7', '#skF_8'))!='#skF_9' | ~r2_hidden(A_2463, k9_relat_1('#skF_8', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_59959])).
% 49.27/37.99  tff(c_59988, plain, (k1_funct_1('#skF_8', '#skF_2'('#skF_9', '#skF_7', '#skF_8'))!='#skF_9'), inference(resolution, [status(thm)], [c_59487, c_59969])).
% 49.27/37.99  tff(c_60008, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_59899, c_59988])).
% 49.27/37.99  tff(c_60010, plain, (k1_relat_1('#skF_8')!='#skF_5'), inference(splitRight, [status(thm)], [c_59923])).
% 49.27/37.99  tff(c_60009, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_59923])).
% 49.27/37.99  tff(c_150137, plain, (![A_4931, A_4932]: (A_4931='#skF_6' | ~v1_funct_2(A_4931, A_4932, '#skF_6') | A_4932='#skF_6' | ~r1_tarski(A_4931, k2_zfmisc_1(A_4932, '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_60009, c_60009, c_60009, c_60009, c_258])).
% 49.27/37.99  tff(c_150155, plain, ('#skF_6'='#skF_8' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6') | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_71, c_150137])).
% 49.27/37.99  tff(c_150163, plain, ('#skF_6'='#skF_8' | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_150155])).
% 49.27/37.99  tff(c_150164, plain, ('#skF_5'='#skF_6'), inference(splitLeft, [status(thm)], [c_150163])).
% 49.27/37.99  tff(c_150177, plain, (k1_relat_1('#skF_8')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_150164, c_60010])).
% 49.27/37.99  tff(c_150199, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_150164, c_62])).
% 49.27/37.99  tff(c_150195, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_150164, c_190])).
% 49.27/37.99  tff(c_150197, plain, (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_150164, c_71])).
% 49.27/37.99  tff(c_59822, plain, (![B_2442, C_2443]: (k1_relset_1(k1_xboole_0, B_2442, C_2443)=k1_xboole_0 | ~v1_funct_2(C_2443, k1_xboole_0, B_2442) | ~m1_subset_1(C_2443, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_2442))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 49.27/37.99  tff(c_59827, plain, (![B_2442, A_7]: (k1_relset_1(k1_xboole_0, B_2442, A_7)=k1_xboole_0 | ~v1_funct_2(A_7, k1_xboole_0, B_2442) | ~r1_tarski(A_7, k2_zfmisc_1(k1_xboole_0, B_2442)))), inference(resolution, [status(thm)], [c_12, c_59822])).
% 49.27/37.99  tff(c_150364, plain, (![B_4938, A_4939]: (k1_relset_1('#skF_6', B_4938, A_4939)='#skF_6' | ~v1_funct_2(A_4939, '#skF_6', B_4938) | ~r1_tarski(A_4939, k2_zfmisc_1('#skF_6', B_4938)))), inference(demodulation, [status(thm), theory('equality')], [c_60009, c_60009, c_60009, c_60009, c_59827])).
% 49.27/37.99  tff(c_150367, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_150197, c_150364])).
% 49.27/37.99  tff(c_150378, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_150199, c_150195, c_150367])).
% 49.27/37.99  tff(c_150380, plain, $false, inference(negUnitSimplification, [status(thm)], [c_150177, c_150378])).
% 49.27/37.99  tff(c_150381, plain, ('#skF_6'='#skF_8'), inference(splitRight, [status(thm)], [c_150163])).
% 49.27/37.99  tff(c_150407, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_150381, c_60])).
% 49.27/37.99  tff(c_203, plain, (![A_89, B_90, A_91]: (k1_relset_1(A_89, B_90, A_91)=k1_relat_1(A_91) | ~r1_tarski(A_91, k2_zfmisc_1(A_89, B_90)))), inference(resolution, [status(thm)], [c_12, c_181])).
% 49.27/37.99  tff(c_218, plain, (![A_89, B_90]: (k1_relset_1(A_89, B_90, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_203])).
% 49.27/37.99  tff(c_60025, plain, (![A_89, B_90]: (k1_relset_1(A_89, B_90, '#skF_6')=k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_60009, c_60009, c_218])).
% 49.27/37.99  tff(c_150391, plain, (![A_89, B_90]: (k1_relset_1(A_89, B_90, '#skF_8')=k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_150381, c_150381, c_60025])).
% 49.27/37.99  tff(c_60389, plain, (![A_2505, A_2506]: (A_2505='#skF_6' | ~v1_funct_2(A_2505, A_2506, '#skF_6') | A_2506='#skF_6' | ~r1_tarski(A_2505, k2_zfmisc_1(A_2506, '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_60009, c_60009, c_60009, c_60009, c_258])).
% 49.27/37.99  tff(c_60403, plain, ('#skF_6'='#skF_8' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6') | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_71, c_60389])).
% 49.27/37.99  tff(c_60410, plain, ('#skF_6'='#skF_8' | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60403])).
% 49.27/37.99  tff(c_60411, plain, ('#skF_5'='#skF_6'), inference(splitLeft, [status(thm)], [c_60410])).
% 49.27/37.99  tff(c_60028, plain, (![A_6]: (r1_tarski('#skF_6', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_60009, c_8])).
% 49.27/37.99  tff(c_60129, plain, (![A_2477, B_2478, C_2479]: (r2_hidden('#skF_3'(A_2477, B_2478, C_2479), B_2478) | k1_relset_1(B_2478, A_2477, C_2479)=B_2478 | ~m1_subset_1(C_2479, k1_zfmisc_1(k2_zfmisc_1(B_2478, A_2477))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 49.27/37.99  tff(c_60134, plain, (r2_hidden('#skF_3'('#skF_6', '#skF_5', '#skF_8'), '#skF_5') | k1_relset_1('#skF_5', '#skF_6', '#skF_8')='#skF_5'), inference(resolution, [status(thm)], [c_60, c_60129])).
% 49.27/37.99  tff(c_60137, plain, (r2_hidden('#skF_3'('#skF_6', '#skF_5', '#skF_8'), '#skF_5') | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_190, c_60134])).
% 49.27/37.99  tff(c_60138, plain, (r2_hidden('#skF_3'('#skF_6', '#skF_5', '#skF_8'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_60010, c_60137])).
% 49.27/37.99  tff(c_60195, plain, (![B_2486]: (r2_hidden('#skF_3'('#skF_6', '#skF_5', '#skF_8'), B_2486) | ~r1_tarski('#skF_5', B_2486))), inference(resolution, [status(thm)], [c_60138, c_2])).
% 49.27/37.99  tff(c_60234, plain, (![B_2494, B_2495]: (r2_hidden('#skF_3'('#skF_6', '#skF_5', '#skF_8'), B_2494) | ~r1_tarski(B_2495, B_2494) | ~r1_tarski('#skF_5', B_2495))), inference(resolution, [status(thm)], [c_60195, c_2])).
% 49.27/37.99  tff(c_60247, plain, (![A_6]: (r2_hidden('#skF_3'('#skF_6', '#skF_5', '#skF_8'), A_6) | ~r1_tarski('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_60028, c_60234])).
% 49.27/37.99  tff(c_60265, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_60247])).
% 49.27/37.99  tff(c_60414, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_60411, c_60265])).
% 49.27/37.99  tff(c_60450, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_140, c_60414])).
% 49.27/37.99  tff(c_60451, plain, ('#skF_6'='#skF_8'), inference(splitRight, [status(thm)], [c_60410])).
% 49.27/37.99  tff(c_59761, plain, (![C_2432, B_2433]: (v1_funct_2(C_2432, k1_xboole_0, B_2433) | k1_relset_1(k1_xboole_0, B_2433, C_2432)!=k1_xboole_0 | ~m1_subset_1(C_2432, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_2433))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 49.27/37.99  tff(c_59781, plain, (![A_2436, B_2437]: (v1_funct_2(A_2436, k1_xboole_0, B_2437) | k1_relset_1(k1_xboole_0, B_2437, A_2436)!=k1_xboole_0 | ~r1_tarski(A_2436, k2_zfmisc_1(k1_xboole_0, B_2437)))), inference(resolution, [status(thm)], [c_12, c_59761])).
% 49.27/37.99  tff(c_59789, plain, (![B_2437]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_2437) | k1_relset_1(k1_xboole_0, B_2437, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_59781])).
% 49.27/37.99  tff(c_59793, plain, (![B_2437]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_2437) | k1_relat_1(k1_xboole_0)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_218, c_59789])).
% 49.27/37.99  tff(c_59794, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_59793])).
% 49.27/37.99  tff(c_60017, plain, (k1_relat_1('#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_60009, c_60009, c_59794])).
% 49.27/37.99  tff(c_60471, plain, (k1_relat_1('#skF_8')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_60451, c_60451, c_60017])).
% 49.27/37.99  tff(c_60468, plain, (![A_89, B_90]: (k1_relset_1(A_89, B_90, '#skF_8')=k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_60451, c_60451, c_60025])).
% 49.27/37.99  tff(c_60472, plain, (![A_6]: (r1_tarski('#skF_8', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_60451, c_60028])).
% 49.27/37.99  tff(c_61102, plain, (![A_2561, B_2562, A_2563]: (r2_hidden('#skF_3'(A_2561, B_2562, A_2563), B_2562) | k1_relset_1(B_2562, A_2561, A_2563)=B_2562 | ~r1_tarski(A_2563, k2_zfmisc_1(B_2562, A_2561)))), inference(resolution, [status(thm)], [c_12, c_60129])).
% 49.27/37.99  tff(c_61839, plain, (![A_2650, B_2651, A_2652, B_2653]: (r2_hidden('#skF_3'(A_2650, B_2651, A_2652), B_2653) | ~r1_tarski(B_2651, B_2653) | k1_relset_1(B_2651, A_2650, A_2652)=B_2651 | ~r1_tarski(A_2652, k2_zfmisc_1(B_2651, A_2650)))), inference(resolution, [status(thm)], [c_61102, c_2])).
% 49.27/37.99  tff(c_26, plain, (![A_20, C_22]: (r2_hidden(k4_tarski(A_20, k1_funct_1(C_22, A_20)), C_22) | ~r2_hidden(A_20, k1_relat_1(C_22)) | ~v1_funct_1(C_22) | ~v1_relat_1(C_22))), inference(cnfTransformation, [status(thm)], [f_68])).
% 49.27/37.99  tff(c_60221, plain, (![A_2489, B_2490, C_2491, E_2492]: (~r2_hidden(k4_tarski('#skF_3'(A_2489, B_2490, C_2491), E_2492), C_2491) | k1_relset_1(B_2490, A_2489, C_2491)=B_2490 | ~m1_subset_1(C_2491, k1_zfmisc_1(k2_zfmisc_1(B_2490, A_2489))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 49.27/37.99  tff(c_60226, plain, (![B_2490, A_2489, C_22]: (k1_relset_1(B_2490, A_2489, C_22)=B_2490 | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(B_2490, A_2489))) | ~r2_hidden('#skF_3'(A_2489, B_2490, C_22), k1_relat_1(C_22)) | ~v1_funct_1(C_22) | ~v1_relat_1(C_22))), inference(resolution, [status(thm)], [c_26, c_60221])).
% 49.27/37.99  tff(c_120358, plain, (![A_4417, B_4418, A_4419]: (~m1_subset_1(A_4417, k1_zfmisc_1(k2_zfmisc_1(B_4418, A_4419))) | ~v1_funct_1(A_4417) | ~v1_relat_1(A_4417) | ~r1_tarski(B_4418, k1_relat_1(A_4417)) | k1_relset_1(B_4418, A_4419, A_4417)=B_4418 | ~r1_tarski(A_4417, k2_zfmisc_1(B_4418, A_4419)))), inference(resolution, [status(thm)], [c_61839, c_60226])).
% 49.27/37.99  tff(c_149359, plain, (![A_4883, B_4884, A_4885]: (~v1_funct_1(A_4883) | ~v1_relat_1(A_4883) | ~r1_tarski(B_4884, k1_relat_1(A_4883)) | k1_relset_1(B_4884, A_4885, A_4883)=B_4884 | ~r1_tarski(A_4883, k2_zfmisc_1(B_4884, A_4885)))), inference(resolution, [status(thm)], [c_12, c_120358])).
% 49.27/37.99  tff(c_149414, plain, (![A_4888, A_4889]: (~v1_funct_1(A_4888) | ~v1_relat_1(A_4888) | k1_relset_1('#skF_8', A_4889, A_4888)='#skF_8' | ~r1_tarski(A_4888, k2_zfmisc_1('#skF_8', A_4889)))), inference(resolution, [status(thm)], [c_60472, c_149359])).
% 49.27/37.99  tff(c_149446, plain, (![A_4889]: (~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | k1_relset_1('#skF_8', A_4889, '#skF_8')='#skF_8')), inference(resolution, [status(thm)], [c_60472, c_149414])).
% 49.27/37.99  tff(c_149460, plain, (k1_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_60468, c_88, c_64, c_149446])).
% 49.27/37.99  tff(c_149462, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60471, c_149460])).
% 49.27/37.99  tff(c_149464, plain, (r1_tarski('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_60247])).
% 49.27/37.99  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 49.27/37.99  tff(c_153, plain, (![C_77, B_78, A_79]: (r2_hidden(C_77, B_78) | ~r2_hidden(C_77, A_79) | ~r1_tarski(A_79, B_78))), inference(cnfTransformation, [status(thm)], [f_32])).
% 49.27/37.99  tff(c_167, plain, (![A_81, B_82, B_83]: (r2_hidden('#skF_1'(A_81, B_82), B_83) | ~r1_tarski(A_81, B_83) | r1_tarski(A_81, B_82))), inference(resolution, [status(thm)], [c_6, c_153])).
% 49.27/38.00  tff(c_59538, plain, (![A_2401, B_2402, B_2403, B_2404]: (r2_hidden('#skF_1'(A_2401, B_2402), B_2403) | ~r1_tarski(B_2404, B_2403) | ~r1_tarski(A_2401, B_2404) | r1_tarski(A_2401, B_2402))), inference(resolution, [status(thm)], [c_167, c_2])).
% 49.27/38.00  tff(c_59551, plain, (![A_2405, B_2406, A_2407]: (r2_hidden('#skF_1'(A_2405, B_2406), A_2407) | ~r1_tarski(A_2405, k1_xboole_0) | r1_tarski(A_2405, B_2406))), inference(resolution, [status(thm)], [c_8, c_59538])).
% 49.27/38.00  tff(c_59573, plain, (![A_2405, A_2407]: (~r1_tarski(A_2405, k1_xboole_0) | r1_tarski(A_2405, A_2407))), inference(resolution, [status(thm)], [c_59551, c_4])).
% 49.27/38.00  tff(c_60020, plain, (![A_2405, A_2407]: (~r1_tarski(A_2405, '#skF_6') | r1_tarski(A_2405, A_2407))), inference(demodulation, [status(thm), theory('equality')], [c_60009, c_59573])).
% 49.27/38.00  tff(c_149479, plain, (![A_2407]: (r1_tarski('#skF_5', A_2407))), inference(resolution, [status(thm)], [c_149464, c_60020])).
% 49.27/38.00  tff(c_60254, plain, (r2_hidden('#skF_3'('#skF_6', '#skF_5', '#skF_8'), k2_zfmisc_1('#skF_5', '#skF_6')) | ~r1_tarski('#skF_5', '#skF_8')), inference(resolution, [status(thm)], [c_71, c_60234])).
% 49.27/38.00  tff(c_60255, plain, (~r1_tarski('#skF_5', '#skF_8')), inference(splitLeft, [status(thm)], [c_60254])).
% 49.27/38.00  tff(c_149496, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_149479, c_60255])).
% 49.27/38.00  tff(c_149498, plain, (r1_tarski('#skF_5', '#skF_8')), inference(splitRight, [status(thm)], [c_60254])).
% 49.27/38.00  tff(c_149770, plain, (![A_4910, A_4911]: (A_4910='#skF_6' | ~v1_funct_2(A_4910, A_4911, '#skF_6') | A_4911='#skF_6' | ~r1_tarski(A_4910, k2_zfmisc_1(A_4911, '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_60009, c_60009, c_60009, c_60009, c_258])).
% 49.27/38.00  tff(c_149784, plain, ('#skF_6'='#skF_8' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6') | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_71, c_149770])).
% 49.27/38.00  tff(c_149791, plain, ('#skF_6'='#skF_8' | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_149784])).
% 49.27/38.00  tff(c_149792, plain, ('#skF_5'='#skF_6'), inference(splitLeft, [status(thm)], [c_149791])).
% 49.27/38.00  tff(c_149639, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_60247])).
% 49.27/38.00  tff(c_149800, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_149792, c_149639])).
% 49.27/38.00  tff(c_149841, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60028, c_149800])).
% 49.27/38.00  tff(c_149842, plain, ('#skF_6'='#skF_8'), inference(splitRight, [status(thm)], [c_149791])).
% 49.27/38.00  tff(c_149848, plain, (~r1_tarski('#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_149842, c_149639])).
% 49.27/38.00  tff(c_149883, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_149498, c_149848])).
% 49.27/38.00  tff(c_149884, plain, (![A_6]: (r2_hidden('#skF_3'('#skF_6', '#skF_5', '#skF_8'), A_6))), inference(splitRight, [status(thm)], [c_60247])).
% 49.27/38.00  tff(c_150384, plain, (![A_6]: (r2_hidden('#skF_3'('#skF_8', '#skF_5', '#skF_8'), A_6))), inference(demodulation, [status(thm), theory('equality')], [c_150381, c_149884])).
% 49.27/38.00  tff(c_151956, plain, (![B_5098, A_5099, C_5100]: (k1_relset_1(B_5098, A_5099, C_5100)=B_5098 | ~m1_subset_1(C_5100, k1_zfmisc_1(k2_zfmisc_1(B_5098, A_5099))) | ~r2_hidden('#skF_3'(A_5099, B_5098, C_5100), k1_relat_1(C_5100)) | ~v1_funct_1(C_5100) | ~v1_relat_1(C_5100))), inference(resolution, [status(thm)], [c_26, c_60221])).
% 49.27/38.00  tff(c_151968, plain, (k1_relset_1('#skF_5', '#skF_8', '#skF_8')='#skF_5' | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_8'))) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_150384, c_151956])).
% 49.27/38.00  tff(c_151973, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_150407, c_150391, c_151968])).
% 49.27/38.00  tff(c_151975, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60010, c_151973])).
% 49.27/38.00  tff(c_151977, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_59793])).
% 49.27/38.00  tff(c_152519, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_152505, c_152505, c_151977])).
% 49.27/38.00  tff(c_152904, plain, (k1_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_152888, c_152888, c_152519])).
% 49.27/38.00  tff(c_152940, plain, (![A_14, B_15]: (r2_hidden('#skF_2'(A_14, B_15, '#skF_8'), '#skF_8') | ~r2_hidden(A_14, k9_relat_1('#skF_8', B_15)) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_152904, c_24])).
% 49.27/38.00  tff(c_153163, plain, (![A_5229, B_5230]: (r2_hidden('#skF_2'(A_5229, B_5230, '#skF_8'), '#skF_8') | ~r2_hidden(A_5229, k9_relat_1('#skF_8', B_5230)))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_152940])).
% 49.27/38.00  tff(c_153167, plain, (![A_5229, B_5230, B_2]: (r2_hidden('#skF_2'(A_5229, B_5230, '#skF_8'), B_2) | ~r1_tarski('#skF_8', B_2) | ~r2_hidden(A_5229, k9_relat_1('#skF_8', B_5230)))), inference(resolution, [status(thm)], [c_153163, c_2])).
% 49.27/38.00  tff(c_153172, plain, (![A_5231, B_5232, B_5233]: (r2_hidden('#skF_2'(A_5231, B_5232, '#skF_8'), B_5233) | ~r2_hidden(A_5231, k9_relat_1('#skF_8', B_5232)))), inference(demodulation, [status(thm), theory('equality')], [c_152906, c_153167])).
% 49.27/38.00  tff(c_153178, plain, (![A_5231]: (k1_funct_1('#skF_8', '#skF_2'(A_5231, '#skF_7', '#skF_8'))!='#skF_9' | ~v1_relat_1('#skF_8') | ~r2_hidden(A_5231, k9_relat_1('#skF_8', '#skF_7')))), inference(resolution, [status(thm)], [c_153172, c_250])).
% 49.27/38.00  tff(c_153264, plain, (![A_5244]: (k1_funct_1('#skF_8', '#skF_2'(A_5244, '#skF_7', '#skF_8'))!='#skF_9' | ~r2_hidden(A_5244, k9_relat_1('#skF_8', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_153178])).
% 49.27/38.00  tff(c_153315, plain, (k1_funct_1('#skF_8', '#skF_2'('#skF_9', '#skF_7', '#skF_8'))!='#skF_9'), inference(resolution, [status(thm)], [c_59487, c_153264])).
% 49.27/38.00  tff(c_153576, plain, (![C_5283, A_5284, B_5285]: (k1_funct_1(C_5283, '#skF_2'(A_5284, B_5285, C_5283))=A_5284 | ~v1_funct_1(C_5283) | ~r2_hidden(A_5284, k9_relat_1(C_5283, B_5285)) | ~v1_relat_1(C_5283))), inference(resolution, [status(thm)], [c_59575, c_28])).
% 49.27/38.00  tff(c_153607, plain, (k1_funct_1('#skF_8', '#skF_2'('#skF_9', '#skF_7', '#skF_8'))='#skF_9' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_59487, c_153576])).
% 49.27/38.00  tff(c_153629, plain, (k1_funct_1('#skF_8', '#skF_2'('#skF_9', '#skF_7', '#skF_8'))='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_153607])).
% 49.27/38.00  tff(c_153631, plain, $false, inference(negUnitSimplification, [status(thm)], [c_153315, c_153629])).
% 49.27/38.00  tff(c_153633, plain, (r1_tarski('#skF_5', k1_xboole_0)), inference(splitRight, [status(thm)], [c_152431])).
% 49.27/38.00  tff(c_153706, plain, (![A_5286]: (r1_tarski('#skF_5', A_5286))), inference(resolution, [status(thm)], [c_153633, c_59573])).
% 49.27/38.00  tff(c_153763, plain, (![A_107]: (k1_xboole_0='#skF_5' | ~v1_funct_2('#skF_5', A_107, k1_xboole_0) | k1_xboole_0=A_107)), inference(resolution, [status(thm)], [c_153706, c_258])).
% 49.27/38.00  tff(c_154025, plain, (![A_107]: ('#skF_5'='#skF_6' | ~v1_funct_2('#skF_5', A_107, '#skF_6') | A_107='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_153800, c_153800, c_153800, c_153763])).
% 49.27/38.00  tff(c_154026, plain, ('#skF_5'='#skF_6'), inference(splitLeft, [status(thm)], [c_154025])).
% 49.27/38.00  tff(c_154034, plain, (k1_relat_1('#skF_8')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_154026, c_152391])).
% 49.27/38.00  tff(c_154056, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_154026, c_62])).
% 49.27/38.00  tff(c_154052, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_154026, c_190])).
% 49.27/38.00  tff(c_154054, plain, (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_154026, c_71])).
% 49.27/38.00  tff(c_152081, plain, (![B_5114, C_5115]: (k1_relset_1(k1_xboole_0, B_5114, C_5115)=k1_xboole_0 | ~v1_funct_2(C_5115, k1_xboole_0, B_5114) | ~m1_subset_1(C_5115, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_5114))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 49.27/38.00  tff(c_152086, plain, (![B_5114, A_7]: (k1_relset_1(k1_xboole_0, B_5114, A_7)=k1_xboole_0 | ~v1_funct_2(A_7, k1_xboole_0, B_5114) | ~r1_tarski(A_7, k2_zfmisc_1(k1_xboole_0, B_5114)))), inference(resolution, [status(thm)], [c_12, c_152081])).
% 49.27/38.00  tff(c_154339, plain, (![B_5342, A_5343]: (k1_relset_1('#skF_6', B_5342, A_5343)='#skF_6' | ~v1_funct_2(A_5343, '#skF_6', B_5342) | ~r1_tarski(A_5343, k2_zfmisc_1('#skF_6', B_5342)))), inference(demodulation, [status(thm), theory('equality')], [c_153800, c_153800, c_153800, c_153800, c_152086])).
% 49.27/38.00  tff(c_154345, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_154054, c_154339])).
% 49.27/38.00  tff(c_154357, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_154056, c_154052, c_154345])).
% 49.27/38.00  tff(c_154359, plain, $false, inference(negUnitSimplification, [status(thm)], [c_154034, c_154357])).
% 49.27/38.00  tff(c_154361, plain, ('#skF_5'!='#skF_6'), inference(splitRight, [status(thm)], [c_154025])).
% 49.27/38.00  tff(c_154515, plain, (![A_5365, A_5366]: (A_5365='#skF_6' | ~v1_funct_2(A_5365, A_5366, '#skF_6') | A_5366='#skF_6' | ~r1_tarski(A_5365, k2_zfmisc_1(A_5366, '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_153800, c_153800, c_153800, c_153800, c_258])).
% 49.27/38.00  tff(c_154533, plain, ('#skF_6'='#skF_8' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6') | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_71, c_154515])).
% 49.27/38.00  tff(c_154544, plain, ('#skF_6'='#skF_8' | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_154533])).
% 49.27/38.00  tff(c_154545, plain, ('#skF_6'='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_154361, c_154544])).
% 49.27/38.00  tff(c_153822, plain, (![A_6]: (r1_tarski('#skF_6', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_153800, c_8])).
% 49.27/38.00  tff(c_154562, plain, (![A_6]: (r1_tarski('#skF_8', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_154545, c_153822])).
% 49.27/38.00  tff(c_153812, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_153800, c_153800, c_151977])).
% 49.27/38.00  tff(c_154561, plain, (k1_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_154545, c_154545, c_153812])).
% 49.27/38.00  tff(c_154630, plain, (![A_14, B_15]: (r2_hidden('#skF_2'(A_14, B_15, '#skF_8'), '#skF_8') | ~r2_hidden(A_14, k9_relat_1('#skF_8', B_15)) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_154561, c_24])).
% 49.27/38.00  tff(c_154854, plain, (![A_5394, B_5395]: (r2_hidden('#skF_2'(A_5394, B_5395, '#skF_8'), '#skF_8') | ~r2_hidden(A_5394, k9_relat_1('#skF_8', B_5395)))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_154630])).
% 49.27/38.00  tff(c_154858, plain, (![A_5394, B_5395, B_2]: (r2_hidden('#skF_2'(A_5394, B_5395, '#skF_8'), B_2) | ~r1_tarski('#skF_8', B_2) | ~r2_hidden(A_5394, k9_relat_1('#skF_8', B_5395)))), inference(resolution, [status(thm)], [c_154854, c_2])).
% 49.27/38.00  tff(c_154865, plain, (![A_5396, B_5397, B_5398]: (r2_hidden('#skF_2'(A_5396, B_5397, '#skF_8'), B_5398) | ~r2_hidden(A_5396, k9_relat_1('#skF_8', B_5397)))), inference(demodulation, [status(thm), theory('equality')], [c_154562, c_154858])).
% 49.27/38.00  tff(c_154871, plain, (![A_5396]: (k1_funct_1('#skF_8', '#skF_2'(A_5396, '#skF_7', '#skF_8'))!='#skF_9' | ~v1_relat_1('#skF_8') | ~r2_hidden(A_5396, k9_relat_1('#skF_8', '#skF_7')))), inference(resolution, [status(thm)], [c_154865, c_250])).
% 49.27/38.00  tff(c_154975, plain, (![A_5411]: (k1_funct_1('#skF_8', '#skF_2'(A_5411, '#skF_7', '#skF_8'))!='#skF_9' | ~r2_hidden(A_5411, k9_relat_1('#skF_8', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_154871])).
% 49.27/38.00  tff(c_155016, plain, (k1_funct_1('#skF_8', '#skF_2'('#skF_9', '#skF_7', '#skF_8'))!='#skF_9'), inference(resolution, [status(thm)], [c_59487, c_154975])).
% 49.27/38.00  tff(c_155195, plain, (![C_5441, A_5442, B_5443]: (k1_funct_1(C_5441, '#skF_2'(A_5442, B_5443, C_5441))=A_5442 | ~v1_funct_1(C_5441) | ~r2_hidden(A_5442, k9_relat_1(C_5441, B_5443)) | ~v1_relat_1(C_5441))), inference(resolution, [status(thm)], [c_59575, c_28])).
% 49.27/38.00  tff(c_155219, plain, (k1_funct_1('#skF_8', '#skF_2'('#skF_9', '#skF_7', '#skF_8'))='#skF_9' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_59487, c_155195])).
% 49.27/38.00  tff(c_155239, plain, (k1_funct_1('#skF_8', '#skF_2'('#skF_9', '#skF_7', '#skF_8'))='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_155219])).
% 49.27/38.00  tff(c_155241, plain, $false, inference(negUnitSimplification, [status(thm)], [c_155016, c_155239])).
% 49.27/38.00  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 49.27/38.00  
% 49.27/38.00  Inference rules
% 49.27/38.00  ----------------------
% 49.27/38.00  #Ref     : 0
% 49.27/38.00  #Sup     : 33698
% 49.27/38.00  #Fact    : 0
% 49.27/38.00  #Define  : 0
% 49.27/38.00  #Split   : 207
% 49.27/38.00  #Chain   : 0
% 49.27/38.00  #Close   : 0
% 49.27/38.00  
% 49.27/38.00  Ordering : KBO
% 49.27/38.00  
% 49.27/38.00  Simplification rules
% 49.27/38.00  ----------------------
% 49.27/38.00  #Subsume      : 15559
% 49.27/38.00  #Demod        : 26381
% 49.27/38.00  #Tautology    : 3357
% 49.27/38.00  #SimpNegUnit  : 234
% 49.27/38.00  #BackRed      : 800
% 49.27/38.00  
% 49.27/38.00  #Partial instantiations: 0
% 49.27/38.00  #Strategies tried      : 1
% 49.27/38.00  
% 49.27/38.00  Timing (in seconds)
% 49.27/38.00  ----------------------
% 49.27/38.00  Preprocessing        : 0.36
% 49.27/38.00  Parsing              : 0.19
% 49.27/38.00  CNF conversion       : 0.03
% 49.27/38.00  Main loop            : 36.80
% 49.27/38.00  Inferencing          : 5.22
% 49.27/38.00  Reduction            : 9.23
% 49.27/38.00  Demodulation         : 6.51
% 49.27/38.00  BG Simplification    : 0.45
% 49.27/38.00  Subsumption          : 19.86
% 49.27/38.00  Abstraction          : 0.84
% 49.27/38.00  MUC search           : 0.00
% 49.27/38.00  Cooper               : 0.00
% 49.27/38.00  Total                : 37.24
% 49.27/38.00  Index Insertion      : 0.00
% 49.27/38.00  Index Deletion       : 0.00
% 49.27/38.00  Index Matching       : 0.00
% 49.27/38.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
