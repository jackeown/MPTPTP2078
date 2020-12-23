%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:06 EST 2020

% Result     : Theorem 4.45s
% Output     : CNFRefutation 4.61s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 607 expanded)
%              Number of leaves         :   39 ( 228 expanded)
%              Depth                    :   19
%              Number of atoms          :  184 (1988 expanded)
%              Number of equality atoms :   34 ( 386 expanded)
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

tff(f_161,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t191_funct_2)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_109,axiom,(
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

tff(f_139,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_122,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_66,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_107,plain,(
    ! [C_62,A_63,B_64] :
      ( v1_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_111,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_107])).

tff(c_14,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_145,plain,(
    ! [A_79,B_80,C_81] :
      ( k2_relset_1(A_79,B_80,C_81) = k2_relat_1(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_149,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_145])).

tff(c_62,plain,(
    ~ r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_155,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_62])).

tff(c_162,plain,
    ( ~ v5_relat_1('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_14,c_155])).

tff(c_165,plain,(
    ~ v5_relat_1('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_162])).

tff(c_70,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_68,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_150,plain,(
    ! [A_82,B_83,C_84] :
      ( k1_relset_1(A_82,B_83,C_84) = k1_relat_1(C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_154,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_150])).

tff(c_321,plain,(
    ! [B_106,A_107,C_108] :
      ( k1_xboole_0 = B_106
      | k1_relset_1(A_107,B_106,C_108) = A_107
      | ~ v1_funct_2(C_108,A_107,B_106)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_107,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_327,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_321])).

tff(c_331,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_154,c_327])).

tff(c_332,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_331])).

tff(c_539,plain,(
    ! [C_139,B_140] :
      ( r2_hidden('#skF_1'(k1_relat_1(C_139),B_140,C_139),k1_relat_1(C_139))
      | m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_139),B_140)))
      | ~ v1_funct_1(C_139)
      | ~ v1_relat_1(C_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_545,plain,(
    ! [B_140] :
      ( r2_hidden('#skF_1'('#skF_3',B_140,'#skF_5'),k1_relat_1('#skF_5'))
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),B_140)))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_539])).

tff(c_554,plain,(
    ! [B_141] :
      ( r2_hidden('#skF_1'('#skF_3',B_141,'#skF_5'),'#skF_3')
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_141))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_70,c_332,c_332,c_545])).

tff(c_18,plain,(
    ! [C_13,B_12,A_11] :
      ( v5_relat_1(C_13,B_12)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_606,plain,(
    ! [B_142] :
      ( v5_relat_1('#skF_5',B_142)
      | r2_hidden('#skF_1'('#skF_3',B_142,'#skF_5'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_554,c_18])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,B_5)
      | ~ r2_hidden(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_610,plain,(
    ! [B_142] :
      ( m1_subset_1('#skF_1'('#skF_3',B_142,'#skF_5'),'#skF_3')
      | v5_relat_1('#skF_5',B_142) ) ),
    inference(resolution,[status(thm)],[c_606,c_10])).

tff(c_74,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_636,plain,(
    ! [A_151,B_152,C_153,D_154] :
      ( k3_funct_2(A_151,B_152,C_153,D_154) = k1_funct_1(C_153,D_154)
      | ~ m1_subset_1(D_154,A_151)
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k2_zfmisc_1(A_151,B_152)))
      | ~ v1_funct_2(C_153,A_151,B_152)
      | ~ v1_funct_1(C_153)
      | v1_xboole_0(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_642,plain,(
    ! [B_152,C_153,B_142] :
      ( k3_funct_2('#skF_3',B_152,C_153,'#skF_1'('#skF_3',B_142,'#skF_5')) = k1_funct_1(C_153,'#skF_1'('#skF_3',B_142,'#skF_5'))
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_152)))
      | ~ v1_funct_2(C_153,'#skF_3',B_152)
      | ~ v1_funct_1(C_153)
      | v1_xboole_0('#skF_3')
      | v5_relat_1('#skF_5',B_142) ) ),
    inference(resolution,[status(thm)],[c_610,c_636])).

tff(c_741,plain,(
    ! [B_158,C_159,B_160] :
      ( k3_funct_2('#skF_3',B_158,C_159,'#skF_1'('#skF_3',B_160,'#skF_5')) = k1_funct_1(C_159,'#skF_1'('#skF_3',B_160,'#skF_5'))
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_158)))
      | ~ v1_funct_2(C_159,'#skF_3',B_158)
      | ~ v1_funct_1(C_159)
      | v5_relat_1('#skF_5',B_160) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_642])).

tff(c_749,plain,(
    ! [B_160] :
      ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'('#skF_3',B_160,'#skF_5')) = k1_funct_1('#skF_5','#skF_1'('#skF_3',B_160,'#skF_5'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5')
      | v5_relat_1('#skF_5',B_160) ) ),
    inference(resolution,[status(thm)],[c_66,c_741])).

tff(c_762,plain,(
    ! [B_161] :
      ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'('#skF_3',B_161,'#skF_5')) = k1_funct_1('#skF_5','#skF_1'('#skF_3',B_161,'#skF_5'))
      | v5_relat_1('#skF_5',B_161) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_749])).

tff(c_64,plain,(
    ! [E_53] :
      ( r2_hidden(k3_funct_2('#skF_3','#skF_4','#skF_5',E_53),'#skF_2')
      | ~ m1_subset_1(E_53,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_781,plain,(
    ! [B_163] :
      ( r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_163,'#skF_5')),'#skF_2')
      | ~ m1_subset_1('#skF_1'('#skF_3',B_163,'#skF_5'),'#skF_3')
      | v5_relat_1('#skF_5',B_163) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_762,c_64])).

tff(c_532,plain,(
    ! [C_136,B_137] :
      ( ~ r2_hidden(k1_funct_1(C_136,'#skF_1'(k1_relat_1(C_136),B_137,C_136)),B_137)
      | v1_funct_2(C_136,k1_relat_1(C_136),B_137)
      | ~ v1_funct_1(C_136)
      | ~ v1_relat_1(C_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_535,plain,(
    ! [B_137] :
      ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_137,'#skF_5')),B_137)
      | v1_funct_2('#skF_5',k1_relat_1('#skF_5'),B_137)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_532])).

tff(c_537,plain,(
    ! [B_137] :
      ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_137,'#skF_5')),B_137)
      | v1_funct_2('#skF_5','#skF_3',B_137) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_70,c_332,c_535])).

tff(c_789,plain,
    ( v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3')
    | v5_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_781,c_537])).

tff(c_798,plain,
    ( v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_165,c_789])).

tff(c_800,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_798])).

tff(c_809,plain,(
    v5_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_610,c_800])).

tff(c_818,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_165,c_809])).

tff(c_820,plain,(
    m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_798])).

tff(c_612,plain,(
    ! [C_144,B_145] :
      ( ~ r2_hidden(k1_funct_1(C_144,'#skF_1'(k1_relat_1(C_144),B_145,C_144)),B_145)
      | m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_144),B_145)))
      | ~ v1_funct_1(C_144)
      | ~ v1_relat_1(C_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_615,plain,(
    ! [B_145] :
      ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_145,'#skF_5')),B_145)
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),B_145)))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_612])).

tff(c_617,plain,(
    ! [B_145] :
      ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_145,'#skF_5')),B_145)
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_145))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_70,c_332,c_615])).

tff(c_785,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3')
    | v5_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_781,c_617])).

tff(c_795,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_165,c_785])).

tff(c_853,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_820,c_795])).

tff(c_886,plain,(
    v5_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_853,c_18])).

tff(c_917,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_165,c_886])).

tff(c_918,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_331])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_927,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_918,c_8])).

tff(c_112,plain,(
    ! [C_65,B_66,A_67] :
      ( v5_relat_1(C_65,B_66)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_67,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_116,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_112])).

tff(c_84,plain,(
    ! [B_59,A_60] :
      ( B_59 = A_60
      | ~ r1_tarski(B_59,A_60)
      | ~ r1_tarski(A_60,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_93,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_84])).

tff(c_941,plain,(
    ! [A_167] :
      ( A_167 = '#skF_4'
      | ~ r1_tarski(A_167,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_918,c_918,c_93])).

tff(c_964,plain,(
    ! [B_170] :
      ( k2_relat_1(B_170) = '#skF_4'
      | ~ v5_relat_1(B_170,'#skF_4')
      | ~ v1_relat_1(B_170) ) ),
    inference(resolution,[status(thm)],[c_14,c_941])).

tff(c_967,plain,
    ( k2_relat_1('#skF_5') = '#skF_4'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_116,c_964])).

tff(c_970,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_967])).

tff(c_979,plain,(
    ~ r1_tarski('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_970,c_155])).

tff(c_993,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_927,c_979])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n007.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:38:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.45/2.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.61/2.18  
% 4.61/2.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.61/2.18  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 4.61/2.18  
% 4.61/2.18  %Foreground sorts:
% 4.61/2.18  
% 4.61/2.18  
% 4.61/2.18  %Background operators:
% 4.61/2.18  
% 4.61/2.18  
% 4.61/2.18  %Foreground operators:
% 4.61/2.18  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.61/2.18  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.61/2.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.61/2.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.61/2.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.61/2.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.61/2.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.61/2.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.61/2.18  tff('#skF_5', type, '#skF_5': $i).
% 4.61/2.18  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.61/2.18  tff('#skF_2', type, '#skF_2': $i).
% 4.61/2.18  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.61/2.18  tff('#skF_3', type, '#skF_3': $i).
% 4.61/2.18  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.61/2.18  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.61/2.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.61/2.18  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.61/2.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.61/2.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.61/2.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.61/2.18  tff('#skF_4', type, '#skF_4': $i).
% 4.61/2.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.61/2.18  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.61/2.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.61/2.18  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 4.61/2.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.61/2.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.61/2.18  
% 4.61/2.21  tff(f_161, negated_conjecture, ~(![A, B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((![E]: (m1_subset_1(E, B) => r2_hidden(k3_funct_2(B, C, D, E), A))) => r1_tarski(k2_relset_1(B, C, D), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t191_funct_2)).
% 4.61/2.21  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.61/2.21  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 4.61/2.21  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.61/2.21  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.61/2.21  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.61/2.21  tff(f_139, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(C) = A) & (![D]: (r2_hidden(D, A) => r2_hidden(k1_funct_1(C, D), B)))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_funct_2)).
% 4.61/2.21  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.61/2.21  tff(f_37, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 4.61/2.21  tff(f_122, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 4.61/2.21  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.61/2.21  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.61/2.21  tff(c_66, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.61/2.21  tff(c_107, plain, (![C_62, A_63, B_64]: (v1_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.61/2.21  tff(c_111, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_66, c_107])).
% 4.61/2.21  tff(c_14, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.61/2.21  tff(c_145, plain, (![A_79, B_80, C_81]: (k2_relset_1(A_79, B_80, C_81)=k2_relat_1(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.61/2.21  tff(c_149, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_66, c_145])).
% 4.61/2.21  tff(c_62, plain, (~r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.61/2.21  tff(c_155, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_149, c_62])).
% 4.61/2.21  tff(c_162, plain, (~v5_relat_1('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_14, c_155])).
% 4.61/2.21  tff(c_165, plain, (~v5_relat_1('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_162])).
% 4.61/2.21  tff(c_70, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.61/2.21  tff(c_68, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.61/2.21  tff(c_150, plain, (![A_82, B_83, C_84]: (k1_relset_1(A_82, B_83, C_84)=k1_relat_1(C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.61/2.21  tff(c_154, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_66, c_150])).
% 4.61/2.21  tff(c_321, plain, (![B_106, A_107, C_108]: (k1_xboole_0=B_106 | k1_relset_1(A_107, B_106, C_108)=A_107 | ~v1_funct_2(C_108, A_107, B_106) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_107, B_106))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.61/2.21  tff(c_327, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_66, c_321])).
% 4.61/2.21  tff(c_331, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_154, c_327])).
% 4.61/2.21  tff(c_332, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_331])).
% 4.61/2.21  tff(c_539, plain, (![C_139, B_140]: (r2_hidden('#skF_1'(k1_relat_1(C_139), B_140, C_139), k1_relat_1(C_139)) | m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_139), B_140))) | ~v1_funct_1(C_139) | ~v1_relat_1(C_139))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.61/2.21  tff(c_545, plain, (![B_140]: (r2_hidden('#skF_1'('#skF_3', B_140, '#skF_5'), k1_relat_1('#skF_5')) | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), B_140))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_332, c_539])).
% 4.61/2.21  tff(c_554, plain, (![B_141]: (r2_hidden('#skF_1'('#skF_3', B_141, '#skF_5'), '#skF_3') | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_141))))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_70, c_332, c_332, c_545])).
% 4.61/2.21  tff(c_18, plain, (![C_13, B_12, A_11]: (v5_relat_1(C_13, B_12) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.61/2.21  tff(c_606, plain, (![B_142]: (v5_relat_1('#skF_5', B_142) | r2_hidden('#skF_1'('#skF_3', B_142, '#skF_5'), '#skF_3'))), inference(resolution, [status(thm)], [c_554, c_18])).
% 4.61/2.21  tff(c_10, plain, (![A_4, B_5]: (m1_subset_1(A_4, B_5) | ~r2_hidden(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.61/2.21  tff(c_610, plain, (![B_142]: (m1_subset_1('#skF_1'('#skF_3', B_142, '#skF_5'), '#skF_3') | v5_relat_1('#skF_5', B_142))), inference(resolution, [status(thm)], [c_606, c_10])).
% 4.61/2.21  tff(c_74, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.61/2.21  tff(c_636, plain, (![A_151, B_152, C_153, D_154]: (k3_funct_2(A_151, B_152, C_153, D_154)=k1_funct_1(C_153, D_154) | ~m1_subset_1(D_154, A_151) | ~m1_subset_1(C_153, k1_zfmisc_1(k2_zfmisc_1(A_151, B_152))) | ~v1_funct_2(C_153, A_151, B_152) | ~v1_funct_1(C_153) | v1_xboole_0(A_151))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.61/2.21  tff(c_642, plain, (![B_152, C_153, B_142]: (k3_funct_2('#skF_3', B_152, C_153, '#skF_1'('#skF_3', B_142, '#skF_5'))=k1_funct_1(C_153, '#skF_1'('#skF_3', B_142, '#skF_5')) | ~m1_subset_1(C_153, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_152))) | ~v1_funct_2(C_153, '#skF_3', B_152) | ~v1_funct_1(C_153) | v1_xboole_0('#skF_3') | v5_relat_1('#skF_5', B_142))), inference(resolution, [status(thm)], [c_610, c_636])).
% 4.61/2.21  tff(c_741, plain, (![B_158, C_159, B_160]: (k3_funct_2('#skF_3', B_158, C_159, '#skF_1'('#skF_3', B_160, '#skF_5'))=k1_funct_1(C_159, '#skF_1'('#skF_3', B_160, '#skF_5')) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_158))) | ~v1_funct_2(C_159, '#skF_3', B_158) | ~v1_funct_1(C_159) | v5_relat_1('#skF_5', B_160))), inference(negUnitSimplification, [status(thm)], [c_74, c_642])).
% 4.61/2.21  tff(c_749, plain, (![B_160]: (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'('#skF_3', B_160, '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_160, '#skF_5')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | v5_relat_1('#skF_5', B_160))), inference(resolution, [status(thm)], [c_66, c_741])).
% 4.61/2.21  tff(c_762, plain, (![B_161]: (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'('#skF_3', B_161, '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_161, '#skF_5')) | v5_relat_1('#skF_5', B_161))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_749])).
% 4.61/2.21  tff(c_64, plain, (![E_53]: (r2_hidden(k3_funct_2('#skF_3', '#skF_4', '#skF_5', E_53), '#skF_2') | ~m1_subset_1(E_53, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.61/2.21  tff(c_781, plain, (![B_163]: (r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_163, '#skF_5')), '#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', B_163, '#skF_5'), '#skF_3') | v5_relat_1('#skF_5', B_163))), inference(superposition, [status(thm), theory('equality')], [c_762, c_64])).
% 4.61/2.21  tff(c_532, plain, (![C_136, B_137]: (~r2_hidden(k1_funct_1(C_136, '#skF_1'(k1_relat_1(C_136), B_137, C_136)), B_137) | v1_funct_2(C_136, k1_relat_1(C_136), B_137) | ~v1_funct_1(C_136) | ~v1_relat_1(C_136))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.61/2.21  tff(c_535, plain, (![B_137]: (~r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_137, '#skF_5')), B_137) | v1_funct_2('#skF_5', k1_relat_1('#skF_5'), B_137) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_332, c_532])).
% 4.61/2.21  tff(c_537, plain, (![B_137]: (~r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_137, '#skF_5')), B_137) | v1_funct_2('#skF_5', '#skF_3', B_137))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_70, c_332, c_535])).
% 4.61/2.21  tff(c_789, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3') | v5_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_781, c_537])).
% 4.61/2.21  tff(c_798, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_165, c_789])).
% 4.61/2.21  tff(c_800, plain, (~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_798])).
% 4.61/2.21  tff(c_809, plain, (v5_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_610, c_800])).
% 4.61/2.21  tff(c_818, plain, $false, inference(negUnitSimplification, [status(thm)], [c_165, c_809])).
% 4.61/2.21  tff(c_820, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3')), inference(splitRight, [status(thm)], [c_798])).
% 4.61/2.21  tff(c_612, plain, (![C_144, B_145]: (~r2_hidden(k1_funct_1(C_144, '#skF_1'(k1_relat_1(C_144), B_145, C_144)), B_145) | m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_144), B_145))) | ~v1_funct_1(C_144) | ~v1_relat_1(C_144))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.61/2.21  tff(c_615, plain, (![B_145]: (~r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_145, '#skF_5')), B_145) | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), B_145))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_332, c_612])).
% 4.61/2.21  tff(c_617, plain, (![B_145]: (~r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_145, '#skF_5')), B_145) | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_145))))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_70, c_332, c_615])).
% 4.61/2.21  tff(c_785, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3') | v5_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_781, c_617])).
% 4.61/2.21  tff(c_795, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_165, c_785])).
% 4.61/2.21  tff(c_853, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_820, c_795])).
% 4.61/2.21  tff(c_886, plain, (v5_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_853, c_18])).
% 4.61/2.21  tff(c_917, plain, $false, inference(negUnitSimplification, [status(thm)], [c_165, c_886])).
% 4.61/2.21  tff(c_918, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_331])).
% 4.61/2.21  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.61/2.21  tff(c_927, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_918, c_8])).
% 4.61/2.21  tff(c_112, plain, (![C_65, B_66, A_67]: (v5_relat_1(C_65, B_66) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_67, B_66))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.61/2.21  tff(c_116, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_66, c_112])).
% 4.61/2.21  tff(c_84, plain, (![B_59, A_60]: (B_59=A_60 | ~r1_tarski(B_59, A_60) | ~r1_tarski(A_60, B_59))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.61/2.21  tff(c_93, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_84])).
% 4.61/2.21  tff(c_941, plain, (![A_167]: (A_167='#skF_4' | ~r1_tarski(A_167, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_918, c_918, c_93])).
% 4.61/2.21  tff(c_964, plain, (![B_170]: (k2_relat_1(B_170)='#skF_4' | ~v5_relat_1(B_170, '#skF_4') | ~v1_relat_1(B_170))), inference(resolution, [status(thm)], [c_14, c_941])).
% 4.61/2.21  tff(c_967, plain, (k2_relat_1('#skF_5')='#skF_4' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_116, c_964])).
% 4.61/2.21  tff(c_970, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_111, c_967])).
% 4.61/2.21  tff(c_979, plain, (~r1_tarski('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_970, c_155])).
% 4.61/2.21  tff(c_993, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_927, c_979])).
% 4.61/2.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.61/2.21  
% 4.61/2.21  Inference rules
% 4.61/2.21  ----------------------
% 4.61/2.21  #Ref     : 0
% 4.61/2.21  #Sup     : 172
% 4.61/2.21  #Fact    : 0
% 4.61/2.21  #Define  : 0
% 4.61/2.21  #Split   : 7
% 4.61/2.21  #Chain   : 0
% 4.61/2.21  #Close   : 0
% 4.61/2.21  
% 4.61/2.21  Ordering : KBO
% 4.61/2.21  
% 4.61/2.21  Simplification rules
% 4.61/2.21  ----------------------
% 4.61/2.21  #Subsume      : 27
% 4.61/2.21  #Demod        : 178
% 4.61/2.21  #Tautology    : 63
% 4.61/2.21  #SimpNegUnit  : 12
% 4.61/2.21  #BackRed      : 23
% 4.61/2.21  
% 4.61/2.21  #Partial instantiations: 0
% 4.61/2.21  #Strategies tried      : 1
% 4.61/2.21  
% 4.61/2.21  Timing (in seconds)
% 4.61/2.21  ----------------------
% 4.61/2.22  Preprocessing        : 0.57
% 4.61/2.22  Parsing              : 0.29
% 4.61/2.22  CNF conversion       : 0.04
% 4.61/2.22  Main loop            : 0.70
% 4.61/2.22  Inferencing          : 0.26
% 4.61/2.22  Reduction            : 0.23
% 4.61/2.22  Demodulation         : 0.16
% 4.61/2.22  BG Simplification    : 0.04
% 4.61/2.22  Subsumption          : 0.12
% 4.61/2.22  Abstraction          : 0.04
% 4.61/2.22  MUC search           : 0.00
% 4.61/2.22  Cooper               : 0.00
% 4.61/2.22  Total                : 1.35
% 4.61/2.22  Index Insertion      : 0.00
% 4.61/2.22  Index Deletion       : 0.00
% 4.61/2.22  Index Matching       : 0.00
% 4.61/2.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
