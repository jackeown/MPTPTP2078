%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:16 EST 2020

% Result     : Theorem 5.16s
% Output     : CNFRefutation 5.34s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 306 expanded)
%              Number of leaves         :   39 ( 120 expanded)
%              Depth                    :   13
%              Number of atoms          :  216 ( 943 expanded)
%              Number of equality atoms :   61 ( 219 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_145,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( ! [E] :
                  ( m1_subset_1(E,A)
                 => k1_funct_1(C,E) = k1_funct_1(D,E) )
             => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_funct_2)).

tff(f_96,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_106,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_124,axiom,(
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

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_79,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k1_relat_1(A) = k1_relat_1(B)
              & ! [C] :
                  ( r2_hidden(C,k1_relat_1(A))
                 => k1_funct_1(A,C) = k1_funct_1(B,C) ) )
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_45,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(c_58,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_336,plain,(
    ! [C_93,B_94,A_95] :
      ( v1_xboole_0(C_93)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(B_94,A_95)))
      | ~ v1_xboole_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_358,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_336])).

tff(c_363,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_358])).

tff(c_582,plain,(
    ! [A_121,B_122,C_123,D_124] :
      ( r2_relset_1(A_121,B_122,C_123,C_123)
      | ~ m1_subset_1(D_124,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122)))
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_794,plain,(
    ! [C_139] :
      ( r2_relset_1('#skF_3','#skF_4',C_139,C_139)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_58,c_582])).

tff(c_810,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_794])).

tff(c_64,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_144,plain,(
    ! [C_61,A_62,B_63] :
      ( v1_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_165,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_144])).

tff(c_68,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_66,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_472,plain,(
    ! [A_104,B_105,C_106] :
      ( k1_relset_1(A_104,B_105,C_106) = k1_relat_1(C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_495,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_472])).

tff(c_951,plain,(
    ! [B_157,A_158,C_159] :
      ( k1_xboole_0 = B_157
      | k1_relset_1(A_158,B_157,C_159) = A_158
      | ~ v1_funct_2(C_159,A_158,B_157)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(A_158,B_157))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_964,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_951])).

tff(c_982,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_495,c_964])).

tff(c_1011,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_982])).

tff(c_164,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_144])).

tff(c_62,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_60,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_494,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_472])).

tff(c_961,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_951])).

tff(c_979,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_494,c_961])).

tff(c_985,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_979])).

tff(c_233,plain,(
    ! [C_73,A_74,B_75] :
      ( v4_relat_1(C_73,A_74)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_255,plain,(
    v4_relat_1('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_233])).

tff(c_24,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k1_relat_1(B_14),A_13)
      | ~ v4_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_999,plain,(
    ! [A_13] :
      ( r1_tarski('#skF_3',A_13)
      | ~ v4_relat_1('#skF_6',A_13)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_985,c_24])).

tff(c_1111,plain,(
    ! [A_164] :
      ( r1_tarski('#skF_3',A_164)
      | ~ v4_relat_1('#skF_6',A_164) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_999])).

tff(c_1120,plain,(
    r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_255,c_1111])).

tff(c_1121,plain,(
    ! [A_165,B_166] :
      ( r2_hidden('#skF_2'(A_165,B_166),k1_relat_1(A_165))
      | B_166 = A_165
      | k1_relat_1(B_166) != k1_relat_1(A_165)
      | ~ v1_funct_1(B_166)
      | ~ v1_relat_1(B_166)
      | ~ v1_funct_1(A_165)
      | ~ v1_relat_1(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1129,plain,(
    ! [B_166] :
      ( r2_hidden('#skF_2'('#skF_6',B_166),'#skF_3')
      | B_166 = '#skF_6'
      | k1_relat_1(B_166) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_166)
      | ~ v1_relat_1(B_166)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_985,c_1121])).

tff(c_1559,plain,(
    ! [B_224] :
      ( r2_hidden('#skF_2'('#skF_6',B_224),'#skF_3')
      | B_224 = '#skF_6'
      | k1_relat_1(B_224) != '#skF_3'
      | ~ v1_funct_1(B_224)
      | ~ v1_relat_1(B_224) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_62,c_985,c_1129])).

tff(c_18,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_414,plain,(
    ! [A_97,C_98,B_99] :
      ( m1_subset_1(A_97,C_98)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(C_98))
      | ~ r2_hidden(A_97,B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_427,plain,(
    ! [A_97,B_9,A_8] :
      ( m1_subset_1(A_97,B_9)
      | ~ r2_hidden(A_97,A_8)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(resolution,[status(thm)],[c_18,c_414])).

tff(c_1910,plain,(
    ! [B_251,B_252] :
      ( m1_subset_1('#skF_2'('#skF_6',B_251),B_252)
      | ~ r1_tarski('#skF_3',B_252)
      | B_251 = '#skF_6'
      | k1_relat_1(B_251) != '#skF_3'
      | ~ v1_funct_1(B_251)
      | ~ v1_relat_1(B_251) ) ),
    inference(resolution,[status(thm)],[c_1559,c_427])).

tff(c_56,plain,(
    ! [E_45] :
      ( k1_funct_1('#skF_5',E_45) = k1_funct_1('#skF_6',E_45)
      | ~ m1_subset_1(E_45,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_1977,plain,(
    ! [B_251] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_6',B_251)) = k1_funct_1('#skF_6','#skF_2'('#skF_6',B_251))
      | ~ r1_tarski('#skF_3','#skF_3')
      | B_251 = '#skF_6'
      | k1_relat_1(B_251) != '#skF_3'
      | ~ v1_funct_1(B_251)
      | ~ v1_relat_1(B_251) ) ),
    inference(resolution,[status(thm)],[c_1910,c_56])).

tff(c_2417,plain,(
    ! [B_271] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_6',B_271)) = k1_funct_1('#skF_6','#skF_2'('#skF_6',B_271))
      | B_271 = '#skF_6'
      | k1_relat_1(B_271) != '#skF_3'
      | ~ v1_funct_1(B_271)
      | ~ v1_relat_1(B_271) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1120,c_1977])).

tff(c_26,plain,(
    ! [B_19,A_15] :
      ( k1_funct_1(B_19,'#skF_2'(A_15,B_19)) != k1_funct_1(A_15,'#skF_2'(A_15,B_19))
      | B_19 = A_15
      | k1_relat_1(B_19) != k1_relat_1(A_15)
      | ~ v1_funct_1(B_19)
      | ~ v1_relat_1(B_19)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2424,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_5' = '#skF_6'
    | k1_relat_1('#skF_5') != '#skF_3'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2417,c_26])).

tff(c_2431,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_68,c_1011,c_164,c_62,c_985,c_1011,c_2424])).

tff(c_54,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_2451,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2431,c_54])).

tff(c_2464,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_810,c_2451])).

tff(c_2465,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_982])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_2503,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2465,c_2])).

tff(c_2505,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_363,c_2503])).

tff(c_2506,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_979])).

tff(c_2544,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2506,c_2])).

tff(c_2546,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_363,c_2544])).

tff(c_2548,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_358])).

tff(c_14,plain,(
    ! [A_6] : m1_subset_1('#skF_1'(A_6),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3111,plain,(
    ! [B_313,A_314] :
      ( v1_xboole_0('#skF_1'(k1_zfmisc_1(k2_zfmisc_1(B_313,A_314))))
      | ~ v1_xboole_0(A_314) ) ),
    inference(resolution,[status(thm)],[c_14,c_336])).

tff(c_6,plain,(
    ! [B_3,A_2] :
      ( ~ v1_xboole_0(B_3)
      | B_3 = A_2
      | ~ v1_xboole_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2562,plain,(
    ! [A_2] :
      ( A_2 = '#skF_4'
      | ~ v1_xboole_0(A_2) ) ),
    inference(resolution,[status(thm)],[c_2548,c_6])).

tff(c_3171,plain,(
    ! [B_324,A_325] :
      ( '#skF_1'(k1_zfmisc_1(k2_zfmisc_1(B_324,A_325))) = '#skF_4'
      | ~ v1_xboole_0(A_325) ) ),
    inference(resolution,[status(thm)],[c_3111,c_2562])).

tff(c_3194,plain,(
    ! [B_324,A_325] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_324,A_325)))
      | ~ v1_xboole_0(A_325) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3171,c_14])).

tff(c_3128,plain,(
    ! [A_315,B_316,C_317,D_318] :
      ( r2_relset_1(A_315,B_316,C_317,C_317)
      | ~ m1_subset_1(D_318,k1_zfmisc_1(k2_zfmisc_1(A_315,B_316)))
      | ~ m1_subset_1(C_317,k1_zfmisc_1(k2_zfmisc_1(A_315,B_316))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_3660,plain,(
    ! [A_384,B_385,C_386] :
      ( r2_relset_1(A_384,B_385,C_386,C_386)
      | ~ m1_subset_1(C_386,k1_zfmisc_1(k2_zfmisc_1(A_384,B_385))) ) ),
    inference(resolution,[status(thm)],[c_14,c_3128])).

tff(c_3676,plain,(
    ! [B_387,A_388] :
      ( r2_relset_1(B_387,A_388,'#skF_4','#skF_4')
      | ~ v1_xboole_0(A_388) ) ),
    inference(resolution,[status(thm)],[c_3194,c_3660])).

tff(c_359,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_336])).

tff(c_2702,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2548,c_359])).

tff(c_2706,plain,(
    ! [A_276] :
      ( A_276 = '#skF_5'
      | ~ v1_xboole_0(A_276) ) ),
    inference(resolution,[status(thm)],[c_2702,c_6])).

tff(c_2715,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2548,c_2706])).

tff(c_97,plain,(
    ! [B_50,A_51] :
      ( ~ v1_xboole_0(B_50)
      | B_50 = A_51
      | ~ v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_100,plain,(
    ! [A_51] :
      ( k1_xboole_0 = A_51
      | ~ v1_xboole_0(A_51) ) ),
    inference(resolution,[status(thm)],[c_2,c_97])).

tff(c_2561,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2548,c_100])).

tff(c_2547,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_358])).

tff(c_2554,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_2547,c_100])).

tff(c_2665,plain,(
    '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2561,c_2554])).

tff(c_2678,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2665,c_54])).

tff(c_2717,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2715,c_2678])).

tff(c_3679,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_3676,c_2717])).

tff(c_3683,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2548,c_3679])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:23:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.16/1.99  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.23/2.00  
% 5.23/2.00  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.23/2.00  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 5.23/2.00  
% 5.23/2.00  %Foreground sorts:
% 5.23/2.00  
% 5.23/2.00  
% 5.23/2.00  %Background operators:
% 5.23/2.00  
% 5.23/2.00  
% 5.23/2.00  %Foreground operators:
% 5.23/2.00  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.23/2.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.23/2.00  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.23/2.00  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.23/2.00  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.23/2.00  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.23/2.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.23/2.00  tff('#skF_5', type, '#skF_5': $i).
% 5.23/2.00  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.23/2.00  tff('#skF_6', type, '#skF_6': $i).
% 5.23/2.00  tff('#skF_3', type, '#skF_3': $i).
% 5.23/2.00  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.23/2.00  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.23/2.00  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.23/2.00  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.23/2.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.23/2.00  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.23/2.00  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.23/2.00  tff('#skF_4', type, '#skF_4': $i).
% 5.23/2.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.23/2.00  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.23/2.00  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.23/2.00  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.23/2.00  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.23/2.00  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.23/2.00  
% 5.34/2.02  tff(f_145, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (m1_subset_1(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_funct_2)).
% 5.34/2.02  tff(f_96, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 5.34/2.02  tff(f_106, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 5.34/2.02  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.34/2.02  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.34/2.02  tff(f_124, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.34/2.02  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.34/2.02  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 5.34/2.02  tff(f_79, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 5.34/2.02  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.34/2.02  tff(f_55, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 5.34/2.02  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.34/2.02  tff(f_45, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 5.34/2.02  tff(f_36, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 5.34/2.02  tff(c_58, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_145])).
% 5.34/2.02  tff(c_336, plain, (![C_93, B_94, A_95]: (v1_xboole_0(C_93) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(B_94, A_95))) | ~v1_xboole_0(A_95))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.34/2.02  tff(c_358, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_58, c_336])).
% 5.34/2.02  tff(c_363, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_358])).
% 5.34/2.02  tff(c_582, plain, (![A_121, B_122, C_123, D_124]: (r2_relset_1(A_121, B_122, C_123, C_123) | ~m1_subset_1(D_124, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.34/2.02  tff(c_794, plain, (![C_139]: (r2_relset_1('#skF_3', '#skF_4', C_139, C_139) | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))))), inference(resolution, [status(thm)], [c_58, c_582])).
% 5.34/2.02  tff(c_810, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_58, c_794])).
% 5.34/2.02  tff(c_64, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_145])).
% 5.34/2.02  tff(c_144, plain, (![C_61, A_62, B_63]: (v1_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.34/2.02  tff(c_165, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_64, c_144])).
% 5.34/2.02  tff(c_68, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_145])).
% 5.34/2.02  tff(c_66, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_145])).
% 5.34/2.02  tff(c_472, plain, (![A_104, B_105, C_106]: (k1_relset_1(A_104, B_105, C_106)=k1_relat_1(C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.34/2.02  tff(c_495, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_64, c_472])).
% 5.34/2.02  tff(c_951, plain, (![B_157, A_158, C_159]: (k1_xboole_0=B_157 | k1_relset_1(A_158, B_157, C_159)=A_158 | ~v1_funct_2(C_159, A_158, B_157) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(A_158, B_157))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.34/2.02  tff(c_964, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_64, c_951])).
% 5.34/2.02  tff(c_982, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_495, c_964])).
% 5.34/2.02  tff(c_1011, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_982])).
% 5.34/2.02  tff(c_164, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_58, c_144])).
% 5.34/2.02  tff(c_62, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_145])).
% 5.34/2.02  tff(c_60, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_145])).
% 5.34/2.02  tff(c_494, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_58, c_472])).
% 5.34/2.02  tff(c_961, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_58, c_951])).
% 5.34/2.02  tff(c_979, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_494, c_961])).
% 5.34/2.02  tff(c_985, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_979])).
% 5.34/2.02  tff(c_233, plain, (![C_73, A_74, B_75]: (v4_relat_1(C_73, A_74) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.34/2.02  tff(c_255, plain, (v4_relat_1('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_233])).
% 5.34/2.02  tff(c_24, plain, (![B_14, A_13]: (r1_tarski(k1_relat_1(B_14), A_13) | ~v4_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.34/2.02  tff(c_999, plain, (![A_13]: (r1_tarski('#skF_3', A_13) | ~v4_relat_1('#skF_6', A_13) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_985, c_24])).
% 5.34/2.02  tff(c_1111, plain, (![A_164]: (r1_tarski('#skF_3', A_164) | ~v4_relat_1('#skF_6', A_164))), inference(demodulation, [status(thm), theory('equality')], [c_164, c_999])).
% 5.34/2.02  tff(c_1120, plain, (r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_255, c_1111])).
% 5.34/2.02  tff(c_1121, plain, (![A_165, B_166]: (r2_hidden('#skF_2'(A_165, B_166), k1_relat_1(A_165)) | B_166=A_165 | k1_relat_1(B_166)!=k1_relat_1(A_165) | ~v1_funct_1(B_166) | ~v1_relat_1(B_166) | ~v1_funct_1(A_165) | ~v1_relat_1(A_165))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.34/2.02  tff(c_1129, plain, (![B_166]: (r2_hidden('#skF_2'('#skF_6', B_166), '#skF_3') | B_166='#skF_6' | k1_relat_1(B_166)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_166) | ~v1_relat_1(B_166) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_985, c_1121])).
% 5.34/2.02  tff(c_1559, plain, (![B_224]: (r2_hidden('#skF_2'('#skF_6', B_224), '#skF_3') | B_224='#skF_6' | k1_relat_1(B_224)!='#skF_3' | ~v1_funct_1(B_224) | ~v1_relat_1(B_224))), inference(demodulation, [status(thm), theory('equality')], [c_164, c_62, c_985, c_1129])).
% 5.34/2.02  tff(c_18, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.34/2.02  tff(c_414, plain, (![A_97, C_98, B_99]: (m1_subset_1(A_97, C_98) | ~m1_subset_1(B_99, k1_zfmisc_1(C_98)) | ~r2_hidden(A_97, B_99))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.34/2.02  tff(c_427, plain, (![A_97, B_9, A_8]: (m1_subset_1(A_97, B_9) | ~r2_hidden(A_97, A_8) | ~r1_tarski(A_8, B_9))), inference(resolution, [status(thm)], [c_18, c_414])).
% 5.34/2.02  tff(c_1910, plain, (![B_251, B_252]: (m1_subset_1('#skF_2'('#skF_6', B_251), B_252) | ~r1_tarski('#skF_3', B_252) | B_251='#skF_6' | k1_relat_1(B_251)!='#skF_3' | ~v1_funct_1(B_251) | ~v1_relat_1(B_251))), inference(resolution, [status(thm)], [c_1559, c_427])).
% 5.34/2.02  tff(c_56, plain, (![E_45]: (k1_funct_1('#skF_5', E_45)=k1_funct_1('#skF_6', E_45) | ~m1_subset_1(E_45, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_145])).
% 5.34/2.02  tff(c_1977, plain, (![B_251]: (k1_funct_1('#skF_5', '#skF_2'('#skF_6', B_251))=k1_funct_1('#skF_6', '#skF_2'('#skF_6', B_251)) | ~r1_tarski('#skF_3', '#skF_3') | B_251='#skF_6' | k1_relat_1(B_251)!='#skF_3' | ~v1_funct_1(B_251) | ~v1_relat_1(B_251))), inference(resolution, [status(thm)], [c_1910, c_56])).
% 5.34/2.02  tff(c_2417, plain, (![B_271]: (k1_funct_1('#skF_5', '#skF_2'('#skF_6', B_271))=k1_funct_1('#skF_6', '#skF_2'('#skF_6', B_271)) | B_271='#skF_6' | k1_relat_1(B_271)!='#skF_3' | ~v1_funct_1(B_271) | ~v1_relat_1(B_271))), inference(demodulation, [status(thm), theory('equality')], [c_1120, c_1977])).
% 5.34/2.02  tff(c_26, plain, (![B_19, A_15]: (k1_funct_1(B_19, '#skF_2'(A_15, B_19))!=k1_funct_1(A_15, '#skF_2'(A_15, B_19)) | B_19=A_15 | k1_relat_1(B_19)!=k1_relat_1(A_15) | ~v1_funct_1(B_19) | ~v1_relat_1(B_19) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.34/2.02  tff(c_2424, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_5'='#skF_6' | k1_relat_1('#skF_5')!='#skF_3' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2417, c_26])).
% 5.34/2.02  tff(c_2431, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_165, c_68, c_1011, c_164, c_62, c_985, c_1011, c_2424])).
% 5.34/2.02  tff(c_54, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_145])).
% 5.34/2.02  tff(c_2451, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2431, c_54])).
% 5.34/2.02  tff(c_2464, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_810, c_2451])).
% 5.34/2.02  tff(c_2465, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_982])).
% 5.34/2.02  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.34/2.02  tff(c_2503, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2465, c_2])).
% 5.34/2.02  tff(c_2505, plain, $false, inference(negUnitSimplification, [status(thm)], [c_363, c_2503])).
% 5.34/2.02  tff(c_2506, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_979])).
% 5.34/2.02  tff(c_2544, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2506, c_2])).
% 5.34/2.02  tff(c_2546, plain, $false, inference(negUnitSimplification, [status(thm)], [c_363, c_2544])).
% 5.34/2.02  tff(c_2548, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_358])).
% 5.34/2.02  tff(c_14, plain, (![A_6]: (m1_subset_1('#skF_1'(A_6), A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.34/2.02  tff(c_3111, plain, (![B_313, A_314]: (v1_xboole_0('#skF_1'(k1_zfmisc_1(k2_zfmisc_1(B_313, A_314)))) | ~v1_xboole_0(A_314))), inference(resolution, [status(thm)], [c_14, c_336])).
% 5.34/2.02  tff(c_6, plain, (![B_3, A_2]: (~v1_xboole_0(B_3) | B_3=A_2 | ~v1_xboole_0(A_2))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.34/2.02  tff(c_2562, plain, (![A_2]: (A_2='#skF_4' | ~v1_xboole_0(A_2))), inference(resolution, [status(thm)], [c_2548, c_6])).
% 5.34/2.02  tff(c_3171, plain, (![B_324, A_325]: ('#skF_1'(k1_zfmisc_1(k2_zfmisc_1(B_324, A_325)))='#skF_4' | ~v1_xboole_0(A_325))), inference(resolution, [status(thm)], [c_3111, c_2562])).
% 5.34/2.02  tff(c_3194, plain, (![B_324, A_325]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_324, A_325))) | ~v1_xboole_0(A_325))), inference(superposition, [status(thm), theory('equality')], [c_3171, c_14])).
% 5.34/2.02  tff(c_3128, plain, (![A_315, B_316, C_317, D_318]: (r2_relset_1(A_315, B_316, C_317, C_317) | ~m1_subset_1(D_318, k1_zfmisc_1(k2_zfmisc_1(A_315, B_316))) | ~m1_subset_1(C_317, k1_zfmisc_1(k2_zfmisc_1(A_315, B_316))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.34/2.02  tff(c_3660, plain, (![A_384, B_385, C_386]: (r2_relset_1(A_384, B_385, C_386, C_386) | ~m1_subset_1(C_386, k1_zfmisc_1(k2_zfmisc_1(A_384, B_385))))), inference(resolution, [status(thm)], [c_14, c_3128])).
% 5.34/2.02  tff(c_3676, plain, (![B_387, A_388]: (r2_relset_1(B_387, A_388, '#skF_4', '#skF_4') | ~v1_xboole_0(A_388))), inference(resolution, [status(thm)], [c_3194, c_3660])).
% 5.34/2.02  tff(c_359, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_64, c_336])).
% 5.34/2.02  tff(c_2702, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2548, c_359])).
% 5.34/2.02  tff(c_2706, plain, (![A_276]: (A_276='#skF_5' | ~v1_xboole_0(A_276))), inference(resolution, [status(thm)], [c_2702, c_6])).
% 5.34/2.02  tff(c_2715, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_2548, c_2706])).
% 5.34/2.02  tff(c_97, plain, (![B_50, A_51]: (~v1_xboole_0(B_50) | B_50=A_51 | ~v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.34/2.02  tff(c_100, plain, (![A_51]: (k1_xboole_0=A_51 | ~v1_xboole_0(A_51))), inference(resolution, [status(thm)], [c_2, c_97])).
% 5.34/2.02  tff(c_2561, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_2548, c_100])).
% 5.34/2.02  tff(c_2547, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_358])).
% 5.34/2.02  tff(c_2554, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_2547, c_100])).
% 5.34/2.02  tff(c_2665, plain, ('#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2561, c_2554])).
% 5.34/2.02  tff(c_2678, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2665, c_54])).
% 5.34/2.02  tff(c_2717, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2715, c_2678])).
% 5.34/2.02  tff(c_3679, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_3676, c_2717])).
% 5.34/2.02  tff(c_3683, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2548, c_3679])).
% 5.34/2.02  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.34/2.02  
% 5.34/2.02  Inference rules
% 5.34/2.02  ----------------------
% 5.34/2.02  #Ref     : 2
% 5.34/2.02  #Sup     : 734
% 5.34/2.02  #Fact    : 0
% 5.34/2.02  #Define  : 0
% 5.34/2.02  #Split   : 10
% 5.34/2.02  #Chain   : 0
% 5.34/2.02  #Close   : 0
% 5.34/2.02  
% 5.34/2.02  Ordering : KBO
% 5.34/2.02  
% 5.34/2.02  Simplification rules
% 5.34/2.02  ----------------------
% 5.34/2.02  #Subsume      : 164
% 5.34/2.02  #Demod        : 982
% 5.34/2.02  #Tautology    : 384
% 5.34/2.02  #SimpNegUnit  : 10
% 5.34/2.02  #BackRed      : 176
% 5.34/2.02  
% 5.34/2.02  #Partial instantiations: 0
% 5.34/2.02  #Strategies tried      : 1
% 5.34/2.02  
% 5.34/2.02  Timing (in seconds)
% 5.34/2.02  ----------------------
% 5.37/2.02  Preprocessing        : 0.36
% 5.37/2.02  Parsing              : 0.19
% 5.37/2.02  CNF conversion       : 0.02
% 5.37/2.02  Main loop            : 0.84
% 5.37/2.02  Inferencing          : 0.27
% 5.37/2.02  Reduction            : 0.32
% 5.37/2.02  Demodulation         : 0.22
% 5.37/2.02  BG Simplification    : 0.03
% 5.37/2.02  Subsumption          : 0.15
% 5.37/2.02  Abstraction          : 0.03
% 5.37/2.02  MUC search           : 0.00
% 5.37/2.02  Cooper               : 0.00
% 5.37/2.02  Total                : 1.24
% 5.37/2.02  Index Insertion      : 0.00
% 5.37/2.02  Index Deletion       : 0.00
% 5.37/2.02  Index Matching       : 0.00
% 5.37/2.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
