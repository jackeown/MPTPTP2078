%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:59 EST 2020

% Result     : Theorem 3.95s
% Output     : CNFRefutation 4.30s
% Verified   : 
% Statistics : Number of formulae       :  217 (3028 expanded)
%              Number of leaves         :   33 ( 943 expanded)
%              Depth                    :   16
%              Number of atoms          :  466 (10550 expanded)
%              Number of equality atoms :  130 (4566 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_115,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( ( B = k1_xboole_0
               => A = k1_xboole_0 )
             => ( r1_partfun1(C,D)
              <=> ! [E] :
                    ( r2_hidden(E,k1_relset_1(A,B,C))
                   => k1_funct_1(C,E) = k1_funct_1(D,E) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_2)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_74,axiom,(
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

tff(f_92,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
           => ( r1_partfun1(A,B)
            <=> ! [C] :
                  ( r2_hidden(C,k1_relat_1(A))
                 => k1_funct_1(A,C) = k1_funct_1(B,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_partfun1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_14,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_96,plain,(
    ! [B_41,A_42] :
      ( v1_relat_1(B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_42))
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_99,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_48,c_96])).

tff(c_105,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_99])).

tff(c_120,plain,(
    ! [C_45,A_46,B_47] :
      ( v4_relat_1(C_45,A_46)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_133,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_120])).

tff(c_12,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(B_7),A_6)
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_54,plain,
    ( r2_hidden('#skF_6',k1_relset_1('#skF_2','#skF_3','#skF_4'))
    | ~ r1_partfun1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_136,plain,(
    ~ r1_partfun1('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_50,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_102,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_42,c_96])).

tff(c_108,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_102])).

tff(c_46,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_40,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_67,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_44,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_164,plain,(
    ! [A_63,B_64,C_65] :
      ( k1_relset_1(A_63,B_64,C_65) = k1_relat_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_178,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_164])).

tff(c_203,plain,(
    ! [B_75,A_76,C_77] :
      ( k1_xboole_0 = B_75
      | k1_relset_1(A_76,B_75,C_77) = A_76
      | ~ v1_funct_2(C_77,A_76,B_75)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_76,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_209,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_203])).

tff(c_221,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_178,c_209])).

tff(c_222,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_221])).

tff(c_277,plain,(
    ! [A_83,B_84] :
      ( r2_hidden('#skF_1'(A_83,B_84),k1_relat_1(A_83))
      | r1_partfun1(A_83,B_84)
      | ~ r1_tarski(k1_relat_1(A_83),k1_relat_1(B_84))
      | ~ v1_funct_1(B_84)
      | ~ v1_relat_1(B_84)
      | ~ v1_funct_1(A_83)
      | ~ v1_relat_1(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_177,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_164])).

tff(c_62,plain,(
    ! [E_36] :
      ( r1_partfun1('#skF_4','#skF_5')
      | k1_funct_1('#skF_5',E_36) = k1_funct_1('#skF_4',E_36)
      | ~ r2_hidden(E_36,k1_relset_1('#skF_2','#skF_3','#skF_4')) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_160,plain,(
    ! [E_36] :
      ( k1_funct_1('#skF_5',E_36) = k1_funct_1('#skF_4',E_36)
      | ~ r2_hidden(E_36,k1_relset_1('#skF_2','#skF_3','#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_62])).

tff(c_180,plain,(
    ! [E_36] :
      ( k1_funct_1('#skF_5',E_36) = k1_funct_1('#skF_4',E_36)
      | ~ r2_hidden(E_36,k1_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_160])).

tff(c_281,plain,(
    ! [B_84] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_84)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_84))
      | r1_partfun1('#skF_4',B_84)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_84))
      | ~ v1_funct_1(B_84)
      | ~ v1_relat_1(B_84)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_277,c_180])).

tff(c_291,plain,(
    ! [B_86] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_86)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_86))
      | r1_partfun1('#skF_4',B_86)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_86))
      | ~ v1_funct_1(B_86)
      | ~ v1_relat_1(B_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_50,c_281])).

tff(c_294,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_5'))
    | r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_291])).

tff(c_299,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_5'))
    | r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_46,c_294])).

tff(c_300,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_5'))
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_299])).

tff(c_304,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_300])).

tff(c_307,plain,
    ( ~ v4_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_304])).

tff(c_311,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_133,c_307])).

tff(c_313,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_300])).

tff(c_312,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_300])).

tff(c_347,plain,(
    ! [B_91,A_92] :
      ( k1_funct_1(B_91,'#skF_1'(A_92,B_91)) != k1_funct_1(A_92,'#skF_1'(A_92,B_91))
      | r1_partfun1(A_92,B_91)
      | ~ r1_tarski(k1_relat_1(A_92),k1_relat_1(B_91))
      | ~ v1_funct_1(B_91)
      | ~ v1_relat_1(B_91)
      | ~ v1_funct_1(A_92)
      | ~ v1_relat_1(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_349,plain,
    ( r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_312,c_347])).

tff(c_352,plain,(
    r1_partfun1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_50,c_108,c_46,c_313,c_222,c_349])).

tff(c_354,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_352])).

tff(c_356,plain,(
    r1_partfun1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_52,plain,
    ( k1_funct_1('#skF_5','#skF_6') != k1_funct_1('#skF_4','#skF_6')
    | ~ r1_partfun1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_359,plain,(
    k1_funct_1('#skF_5','#skF_6') != k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_356,c_52])).

tff(c_384,plain,(
    ! [A_104,B_105,C_106] :
      ( k1_relset_1(A_104,B_105,C_106) = k1_relat_1(C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_398,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_384])).

tff(c_414,plain,(
    ! [B_117,A_118,C_119] :
      ( k1_xboole_0 = B_117
      | k1_relset_1(A_118,B_117,C_119) = A_118
      | ~ v1_funct_2(C_119,A_118,B_117)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_118,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_420,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_414])).

tff(c_432,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_398,c_420])).

tff(c_433,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_432])).

tff(c_397,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_384])).

tff(c_355,plain,(
    r2_hidden('#skF_6',k1_relset_1('#skF_2','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_399,plain,(
    r2_hidden('#skF_6',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_397,c_355])).

tff(c_495,plain,(
    ! [B_128,C_129,A_130] :
      ( k1_funct_1(B_128,C_129) = k1_funct_1(A_130,C_129)
      | ~ r2_hidden(C_129,k1_relat_1(A_130))
      | ~ r1_partfun1(A_130,B_128)
      | ~ r1_tarski(k1_relat_1(A_130),k1_relat_1(B_128))
      | ~ v1_funct_1(B_128)
      | ~ v1_relat_1(B_128)
      | ~ v1_funct_1(A_130)
      | ~ v1_relat_1(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_501,plain,(
    ! [B_128] :
      ( k1_funct_1(B_128,'#skF_6') = k1_funct_1('#skF_4','#skF_6')
      | ~ r1_partfun1('#skF_4',B_128)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_128))
      | ~ v1_funct_1(B_128)
      | ~ v1_relat_1(B_128)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_399,c_495])).

tff(c_508,plain,(
    ! [B_131] :
      ( k1_funct_1(B_131,'#skF_6') = k1_funct_1('#skF_4','#skF_6')
      | ~ r1_partfun1('#skF_4',B_131)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_131))
      | ~ v1_funct_1(B_131)
      | ~ v1_relat_1(B_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_50,c_501])).

tff(c_511,plain,
    ( k1_funct_1('#skF_5','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_433,c_508])).

tff(c_516,plain,
    ( k1_funct_1('#skF_5','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_46,c_356,c_511])).

tff(c_517,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_359,c_516])).

tff(c_527,plain,
    ( ~ v4_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_517])).

tff(c_531,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_133,c_527])).

tff(c_533,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_551,plain,(
    ! [A_136] : k2_zfmisc_1(A_136,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_533,c_533,c_4])).

tff(c_555,plain,(
    v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_551,c_14])).

tff(c_550,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_533,c_533,c_4])).

tff(c_532,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_538,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_533,c_532])).

tff(c_580,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_550,c_538,c_48])).

tff(c_581,plain,(
    ! [B_138,A_139] :
      ( v1_relat_1(B_138)
      | ~ m1_subset_1(B_138,k1_zfmisc_1(A_139))
      | ~ v1_relat_1(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_584,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_580,c_581])).

tff(c_590,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_555,c_584])).

tff(c_1252,plain,(
    ! [C_253,A_254,B_255] :
      ( v4_relat_1(C_253,A_254)
      | ~ m1_subset_1(C_253,k1_zfmisc_1(k2_zfmisc_1(A_254,B_255))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1260,plain,(
    ! [C_257,A_258] :
      ( v4_relat_1(C_257,A_258)
      | ~ m1_subset_1(C_257,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_550,c_1252])).

tff(c_1265,plain,(
    ! [A_258] : v4_relat_1('#skF_4',A_258) ),
    inference(resolution,[status(thm)],[c_580,c_1260])).

tff(c_594,plain,(
    ~ r1_partfun1('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_543,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_538,c_42])).

tff(c_579,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_550,c_543])).

tff(c_587,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_579,c_581])).

tff(c_593,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_555,c_587])).

tff(c_630,plain,(
    ! [C_153,A_154,B_155] :
      ( v4_relat_1(C_153,A_154)
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k2_zfmisc_1(A_154,B_155))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_648,plain,(
    ! [C_157,A_158] :
      ( v4_relat_1(C_157,A_158)
      | ~ m1_subset_1(C_157,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_550,c_630])).

tff(c_653,plain,(
    ! [A_158] : v4_relat_1('#skF_4',A_158) ),
    inference(resolution,[status(thm)],[c_580,c_648])).

tff(c_6,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_560,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_3',B_2) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_533,c_533,c_6])).

tff(c_670,plain,(
    ! [A_164,B_165,C_166] :
      ( k1_relset_1(A_164,B_165,C_166) = k1_relat_1(C_166)
      | ~ m1_subset_1(C_166,k1_zfmisc_1(k2_zfmisc_1(A_164,B_165))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_677,plain,(
    ! [B_167,C_168] :
      ( k1_relset_1('#skF_3',B_167,C_168) = k1_relat_1(C_168)
      | ~ m1_subset_1(C_168,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_560,c_670])).

tff(c_683,plain,(
    ! [B_167] : k1_relset_1('#skF_3',B_167,'#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_579,c_677])).

tff(c_26,plain,(
    ! [C_18,B_17] :
      ( v1_funct_2(C_18,k1_xboole_0,B_17)
      | k1_relset_1(k1_xboole_0,B_17,C_18) != k1_xboole_0
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_64,plain,(
    ! [C_18,B_17] :
      ( v1_funct_2(C_18,k1_xboole_0,B_17)
      | k1_relset_1(k1_xboole_0,B_17,C_18) != k1_xboole_0
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_26])).

tff(c_685,plain,(
    ! [C_169,B_170] :
      ( v1_funct_2(C_169,'#skF_3',B_170)
      | k1_relset_1('#skF_3',B_170,C_169) != '#skF_3'
      | ~ m1_subset_1(C_169,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_533,c_533,c_533,c_533,c_64])).

tff(c_691,plain,(
    ! [B_170] :
      ( v1_funct_2('#skF_5','#skF_3',B_170)
      | k1_relset_1('#skF_3',B_170,'#skF_5') != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_579,c_685])).

tff(c_1041,plain,(
    ! [B_170] :
      ( v1_funct_2('#skF_5','#skF_3',B_170)
      | k1_relat_1('#skF_5') != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_683,c_691])).

tff(c_1042,plain,(
    k1_relat_1('#skF_5') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1041])).

tff(c_544,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_538,c_44])).

tff(c_30,plain,(
    ! [B_17,C_18] :
      ( k1_relset_1(k1_xboole_0,B_17,C_18) = k1_xboole_0
      | ~ v1_funct_2(C_18,k1_xboole_0,B_17)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_63,plain,(
    ! [B_17,C_18] :
      ( k1_relset_1(k1_xboole_0,B_17,C_18) = k1_xboole_0
      | ~ v1_funct_2(C_18,k1_xboole_0,B_17)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_30])).

tff(c_1044,plain,(
    ! [B_217,C_218] :
      ( k1_relset_1('#skF_3',B_217,C_218) = '#skF_3'
      | ~ v1_funct_2(C_218,'#skF_3',B_217)
      | ~ m1_subset_1(C_218,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_533,c_533,c_533,c_533,c_63])).

tff(c_1046,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_5') = '#skF_3'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_544,c_1044])).

tff(c_1049,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_579,c_683,c_1046])).

tff(c_1051,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1042,c_1049])).

tff(c_1053,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1041])).

tff(c_1152,plain,(
    ! [A_235,B_236] :
      ( r2_hidden('#skF_1'(A_235,B_236),k1_relat_1(A_235))
      | r1_partfun1(A_235,B_236)
      | ~ r1_tarski(k1_relat_1(A_235),k1_relat_1(B_236))
      | ~ v1_funct_1(B_236)
      | ~ v1_relat_1(B_236)
      | ~ v1_funct_1(A_235)
      | ~ v1_relat_1(A_235) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_711,plain,(
    ! [B_170] :
      ( v1_funct_2('#skF_5','#skF_3',B_170)
      | k1_relat_1('#skF_5') != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_683,c_691])).

tff(c_712,plain,(
    k1_relat_1('#skF_5') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_711])).

tff(c_721,plain,(
    ! [B_175,C_176] :
      ( k1_relset_1('#skF_3',B_175,C_176) = '#skF_3'
      | ~ v1_funct_2(C_176,'#skF_3',B_175)
      | ~ m1_subset_1(C_176,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_533,c_533,c_533,c_533,c_63])).

tff(c_723,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_5') = '#skF_3'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_544,c_721])).

tff(c_726,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_579,c_683,c_723])).

tff(c_728,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_712,c_726])).

tff(c_730,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_711])).

tff(c_900,plain,(
    ! [A_201,B_202] :
      ( r2_hidden('#skF_1'(A_201,B_202),k1_relat_1(A_201))
      | r1_partfun1(A_201,B_202)
      | ~ r1_tarski(k1_relat_1(A_201),k1_relat_1(B_202))
      | ~ v1_funct_1(B_202)
      | ~ v1_relat_1(B_202)
      | ~ v1_funct_1(A_201)
      | ~ v1_relat_1(A_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_682,plain,(
    ! [B_167] : k1_relset_1('#skF_3',B_167,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_580,c_677])).

tff(c_58,plain,(
    ! [E_36] :
      ( k1_funct_1('#skF_5','#skF_6') != k1_funct_1('#skF_4','#skF_6')
      | k1_funct_1('#skF_5',E_36) = k1_funct_1('#skF_4',E_36)
      | ~ r2_hidden(E_36,k1_relset_1('#skF_2','#skF_3','#skF_4')) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_756,plain,(
    ! [E_36] :
      ( k1_funct_1('#skF_5','#skF_6') != k1_funct_1('#skF_4','#skF_6')
      | k1_funct_1('#skF_5',E_36) = k1_funct_1('#skF_4',E_36)
      | ~ r2_hidden(E_36,k1_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_682,c_538,c_58])).

tff(c_757,plain,(
    k1_funct_1('#skF_5','#skF_6') != k1_funct_1('#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_756])).

tff(c_60,plain,(
    ! [E_36] :
      ( r2_hidden('#skF_6',k1_relset_1('#skF_2','#skF_3','#skF_4'))
      | k1_funct_1('#skF_5',E_36) = k1_funct_1('#skF_4',E_36)
      | ~ r2_hidden(E_36,k1_relset_1('#skF_2','#skF_3','#skF_4')) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_709,plain,(
    ! [E_36] :
      ( r2_hidden('#skF_6',k1_relat_1('#skF_4'))
      | k1_funct_1('#skF_5',E_36) = k1_funct_1('#skF_4',E_36)
      | ~ r2_hidden(E_36,k1_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_682,c_538,c_682,c_538,c_60])).

tff(c_710,plain,(
    r2_hidden('#skF_6',k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_709])).

tff(c_655,plain,(
    ! [E_36] :
      ( r1_partfun1('#skF_4','#skF_5')
      | k1_funct_1('#skF_5',E_36) = k1_funct_1('#skF_4',E_36)
      | ~ r2_hidden(E_36,k1_relset_1('#skF_3','#skF_3','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_538,c_62])).

tff(c_656,plain,(
    ! [E_36] :
      ( k1_funct_1('#skF_5',E_36) = k1_funct_1('#skF_4',E_36)
      | ~ r2_hidden(E_36,k1_relset_1('#skF_3','#skF_3','#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_594,c_655])).

tff(c_810,plain,(
    ! [E_186] :
      ( k1_funct_1('#skF_5',E_186) = k1_funct_1('#skF_4',E_186)
      | ~ r2_hidden(E_186,k1_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_682,c_656])).

tff(c_813,plain,(
    k1_funct_1('#skF_5','#skF_6') = k1_funct_1('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_710,c_810])).

tff(c_817,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_757,c_813])).

tff(c_818,plain,(
    ! [E_36] :
      ( k1_funct_1('#skF_5',E_36) = k1_funct_1('#skF_4',E_36)
      | ~ r2_hidden(E_36,k1_relat_1('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_756])).

tff(c_904,plain,(
    ! [B_202] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_202)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_202))
      | r1_partfun1('#skF_4',B_202)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_202))
      | ~ v1_funct_1(B_202)
      | ~ v1_relat_1(B_202)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_900,c_818])).

tff(c_914,plain,(
    ! [B_204] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_204)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_204))
      | r1_partfun1('#skF_4',B_204)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_204))
      | ~ v1_funct_1(B_204)
      | ~ v1_relat_1(B_204) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_590,c_50,c_904])).

tff(c_917,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_5'))
    | r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_730,c_914])).

tff(c_922,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_5'))
    | r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_593,c_46,c_917])).

tff(c_923,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_5'))
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_594,c_922])).

tff(c_927,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_923])).

tff(c_930,plain,
    ( ~ v4_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_927])).

tff(c_934,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_590,c_653,c_930])).

tff(c_936,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_923])).

tff(c_920,plain,(
    ! [B_204] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_204)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_204))
      | r1_partfun1('#skF_4',B_204)
      | ~ v1_funct_1(B_204)
      | ~ v1_relat_1(B_204)
      | ~ v4_relat_1('#skF_4',k1_relat_1(B_204))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_12,c_914])).

tff(c_926,plain,(
    ! [B_204] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_204)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_204))
      | r1_partfun1('#skF_4',B_204)
      | ~ v1_funct_1(B_204)
      | ~ v1_relat_1(B_204) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_590,c_653,c_920])).

tff(c_1018,plain,(
    ! [B_215,A_216] :
      ( k1_funct_1(B_215,'#skF_1'(A_216,B_215)) != k1_funct_1(A_216,'#skF_1'(A_216,B_215))
      | r1_partfun1(A_216,B_215)
      | ~ r1_tarski(k1_relat_1(A_216),k1_relat_1(B_215))
      | ~ v1_funct_1(B_215)
      | ~ v1_relat_1(B_215)
      | ~ v1_funct_1(A_216)
      | ~ v1_relat_1(A_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1026,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | r1_partfun1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_926,c_1018])).

tff(c_1036,plain,(
    r1_partfun1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_593,c_46,c_590,c_50,c_936,c_730,c_1026])).

tff(c_1038,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_594,c_1036])).

tff(c_1039,plain,(
    ! [E_36] :
      ( k1_funct_1('#skF_5',E_36) = k1_funct_1('#skF_4',E_36)
      | ~ r2_hidden(E_36,k1_relat_1('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_709])).

tff(c_1156,plain,(
    ! [B_236] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_236)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_236))
      | r1_partfun1('#skF_4',B_236)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_236))
      | ~ v1_funct_1(B_236)
      | ~ v1_relat_1(B_236)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1152,c_1039])).

tff(c_1166,plain,(
    ! [B_238] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_238)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_238))
      | r1_partfun1('#skF_4',B_238)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_238))
      | ~ v1_funct_1(B_238)
      | ~ v1_relat_1(B_238) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_590,c_50,c_1156])).

tff(c_1169,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_5'))
    | r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1053,c_1166])).

tff(c_1174,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_5'))
    | r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_593,c_46,c_1169])).

tff(c_1175,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_5'))
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_594,c_1174])).

tff(c_1179,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1175])).

tff(c_1182,plain,
    ( ~ v4_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_1179])).

tff(c_1186,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_590,c_653,c_1182])).

tff(c_1188,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_1175])).

tff(c_1187,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1175])).

tff(c_36,plain,(
    ! [B_25,A_19] :
      ( k1_funct_1(B_25,'#skF_1'(A_19,B_25)) != k1_funct_1(A_19,'#skF_1'(A_19,B_25))
      | r1_partfun1(A_19,B_25)
      | ~ r1_tarski(k1_relat_1(A_19),k1_relat_1(B_25))
      | ~ v1_funct_1(B_25)
      | ~ v1_relat_1(B_25)
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1201,plain,
    ( r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1187,c_36])).

tff(c_1206,plain,(
    r1_partfun1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_590,c_50,c_593,c_46,c_1188,c_1053,c_1201])).

tff(c_1208,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_594,c_1206])).

tff(c_1209,plain,(
    k1_funct_1('#skF_5','#skF_6') != k1_funct_1('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_1210,plain,(
    r1_partfun1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_1272,plain,(
    ! [A_261,B_262,C_263] :
      ( k1_relset_1(A_261,B_262,C_263) = k1_relat_1(C_263)
      | ~ m1_subset_1(C_263,k1_zfmisc_1(k2_zfmisc_1(A_261,B_262))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1279,plain,(
    ! [B_264,C_265] :
      ( k1_relset_1('#skF_3',B_264,C_265) = k1_relat_1(C_265)
      | ~ m1_subset_1(C_265,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_560,c_1272])).

tff(c_1285,plain,(
    ! [B_264] : k1_relset_1('#skF_3',B_264,'#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_579,c_1279])).

tff(c_1348,plain,(
    ! [C_274,B_275] :
      ( v1_funct_2(C_274,'#skF_3',B_275)
      | k1_relset_1('#skF_3',B_275,C_274) != '#skF_3'
      | ~ m1_subset_1(C_274,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_533,c_533,c_533,c_533,c_64])).

tff(c_1352,plain,(
    ! [B_275] :
      ( v1_funct_2('#skF_5','#skF_3',B_275)
      | k1_relset_1('#skF_3',B_275,'#skF_5') != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_579,c_1348])).

tff(c_1356,plain,(
    ! [B_275] :
      ( v1_funct_2('#skF_5','#skF_3',B_275)
      | k1_relat_1('#skF_5') != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1285,c_1352])).

tff(c_1358,plain,(
    k1_relat_1('#skF_5') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1356])).

tff(c_1360,plain,(
    ! [B_276,C_277] :
      ( k1_relset_1('#skF_3',B_276,C_277) = '#skF_3'
      | ~ v1_funct_2(C_277,'#skF_3',B_276)
      | ~ m1_subset_1(C_277,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_533,c_533,c_533,c_533,c_63])).

tff(c_1362,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_5') = '#skF_3'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_544,c_1360])).

tff(c_1365,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_579,c_1285,c_1362])).

tff(c_1367,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1358,c_1365])).

tff(c_1369,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1356])).

tff(c_1284,plain,(
    ! [B_264] : k1_relset_1('#skF_3',B_264,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_580,c_1279])).

tff(c_1211,plain,
    ( r2_hidden('#skF_6',k1_relset_1('#skF_3','#skF_3','#skF_4'))
    | ~ r1_partfun1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_538,c_54])).

tff(c_1212,plain,(
    ~ r1_partfun1('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1211])).

tff(c_1214,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1210,c_1212])).

tff(c_1215,plain,(
    r2_hidden('#skF_6',k1_relset_1('#skF_3','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1211])).

tff(c_1286,plain,(
    r2_hidden('#skF_6',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1284,c_1215])).

tff(c_1471,plain,(
    ! [B_296,C_297,A_298] :
      ( k1_funct_1(B_296,C_297) = k1_funct_1(A_298,C_297)
      | ~ r2_hidden(C_297,k1_relat_1(A_298))
      | ~ r1_partfun1(A_298,B_296)
      | ~ r1_tarski(k1_relat_1(A_298),k1_relat_1(B_296))
      | ~ v1_funct_1(B_296)
      | ~ v1_relat_1(B_296)
      | ~ v1_funct_1(A_298)
      | ~ v1_relat_1(A_298) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1477,plain,(
    ! [B_296] :
      ( k1_funct_1(B_296,'#skF_6') = k1_funct_1('#skF_4','#skF_6')
      | ~ r1_partfun1('#skF_4',B_296)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_296))
      | ~ v1_funct_1(B_296)
      | ~ v1_relat_1(B_296)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1286,c_1471])).

tff(c_1508,plain,(
    ! [B_302] :
      ( k1_funct_1(B_302,'#skF_6') = k1_funct_1('#skF_4','#skF_6')
      | ~ r1_partfun1('#skF_4',B_302)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_302))
      | ~ v1_funct_1(B_302)
      | ~ v1_relat_1(B_302) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_590,c_50,c_1477])).

tff(c_1511,plain,
    ( k1_funct_1('#skF_5','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1369,c_1508])).

tff(c_1516,plain,
    ( k1_funct_1('#skF_5','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_593,c_46,c_1210,c_1511])).

tff(c_1517,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_1209,c_1516])).

tff(c_1523,plain,
    ( ~ v4_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_1517])).

tff(c_1527,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_590,c_1265,c_1523])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:11:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.95/1.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.30/1.75  
% 4.30/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.30/1.75  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.30/1.75  
% 4.30/1.75  %Foreground sorts:
% 4.30/1.75  
% 4.30/1.75  
% 4.30/1.75  %Background operators:
% 4.30/1.75  
% 4.30/1.75  
% 4.30/1.75  %Foreground operators:
% 4.30/1.75  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.30/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.30/1.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.30/1.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.30/1.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.30/1.75  tff('#skF_5', type, '#skF_5': $i).
% 4.30/1.75  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.30/1.75  tff('#skF_6', type, '#skF_6': $i).
% 4.30/1.75  tff('#skF_2', type, '#skF_2': $i).
% 4.30/1.75  tff('#skF_3', type, '#skF_3': $i).
% 4.30/1.75  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.30/1.75  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.30/1.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.30/1.75  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.30/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.30/1.75  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.30/1.75  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.30/1.75  tff('#skF_4', type, '#skF_4': $i).
% 4.30/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.30/1.75  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.30/1.75  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.30/1.75  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.30/1.75  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 4.30/1.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.30/1.75  
% 4.30/1.78  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.30/1.78  tff(f_115, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (r1_partfun1(C, D) <=> (![E]: (r2_hidden(E, k1_relset_1(A, B, C)) => (k1_funct_1(C, E) = k1_funct_1(D, E)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_2)).
% 4.30/1.78  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.30/1.78  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.30/1.78  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 4.30/1.78  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.30/1.78  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.30/1.78  tff(f_92, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) => (r1_partfun1(A, B) <=> (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_partfun1)).
% 4.30/1.78  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.30/1.78  tff(c_14, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.30/1.78  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.30/1.78  tff(c_96, plain, (![B_41, A_42]: (v1_relat_1(B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(A_42)) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.30/1.78  tff(c_99, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_48, c_96])).
% 4.30/1.78  tff(c_105, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_99])).
% 4.30/1.78  tff(c_120, plain, (![C_45, A_46, B_47]: (v4_relat_1(C_45, A_46) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.30/1.78  tff(c_133, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_48, c_120])).
% 4.30/1.78  tff(c_12, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(B_7), A_6) | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.30/1.78  tff(c_54, plain, (r2_hidden('#skF_6', k1_relset_1('#skF_2', '#skF_3', '#skF_4')) | ~r1_partfun1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.30/1.78  tff(c_136, plain, (~r1_partfun1('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_54])).
% 4.30/1.78  tff(c_50, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.30/1.78  tff(c_42, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.30/1.78  tff(c_102, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_42, c_96])).
% 4.30/1.78  tff(c_108, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_102])).
% 4.30/1.78  tff(c_46, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.30/1.78  tff(c_40, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.30/1.78  tff(c_67, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_40])).
% 4.30/1.78  tff(c_44, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.30/1.78  tff(c_164, plain, (![A_63, B_64, C_65]: (k1_relset_1(A_63, B_64, C_65)=k1_relat_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.30/1.78  tff(c_178, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_42, c_164])).
% 4.30/1.78  tff(c_203, plain, (![B_75, A_76, C_77]: (k1_xboole_0=B_75 | k1_relset_1(A_76, B_75, C_77)=A_76 | ~v1_funct_2(C_77, A_76, B_75) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_76, B_75))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.30/1.78  tff(c_209, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_203])).
% 4.30/1.78  tff(c_221, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_178, c_209])).
% 4.30/1.78  tff(c_222, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_67, c_221])).
% 4.30/1.78  tff(c_277, plain, (![A_83, B_84]: (r2_hidden('#skF_1'(A_83, B_84), k1_relat_1(A_83)) | r1_partfun1(A_83, B_84) | ~r1_tarski(k1_relat_1(A_83), k1_relat_1(B_84)) | ~v1_funct_1(B_84) | ~v1_relat_1(B_84) | ~v1_funct_1(A_83) | ~v1_relat_1(A_83))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.30/1.78  tff(c_177, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_164])).
% 4.30/1.78  tff(c_62, plain, (![E_36]: (r1_partfun1('#skF_4', '#skF_5') | k1_funct_1('#skF_5', E_36)=k1_funct_1('#skF_4', E_36) | ~r2_hidden(E_36, k1_relset_1('#skF_2', '#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.30/1.78  tff(c_160, plain, (![E_36]: (k1_funct_1('#skF_5', E_36)=k1_funct_1('#skF_4', E_36) | ~r2_hidden(E_36, k1_relset_1('#skF_2', '#skF_3', '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_136, c_62])).
% 4.30/1.78  tff(c_180, plain, (![E_36]: (k1_funct_1('#skF_5', E_36)=k1_funct_1('#skF_4', E_36) | ~r2_hidden(E_36, k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_177, c_160])).
% 4.30/1.78  tff(c_281, plain, (![B_84]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_84))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_84)) | r1_partfun1('#skF_4', B_84) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_84)) | ~v1_funct_1(B_84) | ~v1_relat_1(B_84) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_277, c_180])).
% 4.30/1.78  tff(c_291, plain, (![B_86]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_86))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_86)) | r1_partfun1('#skF_4', B_86) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_86)) | ~v1_funct_1(B_86) | ~v1_relat_1(B_86))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_50, c_281])).
% 4.30/1.78  tff(c_294, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_5'))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', '#skF_5')) | r1_partfun1('#skF_4', '#skF_5') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_222, c_291])).
% 4.30/1.78  tff(c_299, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_5'))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', '#skF_5')) | r1_partfun1('#skF_4', '#skF_5') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_46, c_294])).
% 4.30/1.78  tff(c_300, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_5'))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', '#skF_5')) | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_136, c_299])).
% 4.30/1.78  tff(c_304, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(splitLeft, [status(thm)], [c_300])).
% 4.30/1.78  tff(c_307, plain, (~v4_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_12, c_304])).
% 4.30/1.78  tff(c_311, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_105, c_133, c_307])).
% 4.30/1.78  tff(c_313, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(splitRight, [status(thm)], [c_300])).
% 4.30/1.78  tff(c_312, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_5'))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_300])).
% 4.30/1.78  tff(c_347, plain, (![B_91, A_92]: (k1_funct_1(B_91, '#skF_1'(A_92, B_91))!=k1_funct_1(A_92, '#skF_1'(A_92, B_91)) | r1_partfun1(A_92, B_91) | ~r1_tarski(k1_relat_1(A_92), k1_relat_1(B_91)) | ~v1_funct_1(B_91) | ~v1_relat_1(B_91) | ~v1_funct_1(A_92) | ~v1_relat_1(A_92))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.30/1.78  tff(c_349, plain, (r1_partfun1('#skF_4', '#skF_5') | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_312, c_347])).
% 4.30/1.78  tff(c_352, plain, (r1_partfun1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_50, c_108, c_46, c_313, c_222, c_349])).
% 4.30/1.78  tff(c_354, plain, $false, inference(negUnitSimplification, [status(thm)], [c_136, c_352])).
% 4.30/1.78  tff(c_356, plain, (r1_partfun1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_54])).
% 4.30/1.78  tff(c_52, plain, (k1_funct_1('#skF_5', '#skF_6')!=k1_funct_1('#skF_4', '#skF_6') | ~r1_partfun1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.30/1.78  tff(c_359, plain, (k1_funct_1('#skF_5', '#skF_6')!=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_356, c_52])).
% 4.30/1.78  tff(c_384, plain, (![A_104, B_105, C_106]: (k1_relset_1(A_104, B_105, C_106)=k1_relat_1(C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.30/1.78  tff(c_398, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_42, c_384])).
% 4.30/1.78  tff(c_414, plain, (![B_117, A_118, C_119]: (k1_xboole_0=B_117 | k1_relset_1(A_118, B_117, C_119)=A_118 | ~v1_funct_2(C_119, A_118, B_117) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_118, B_117))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.30/1.78  tff(c_420, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_414])).
% 4.30/1.78  tff(c_432, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_398, c_420])).
% 4.30/1.78  tff(c_433, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_67, c_432])).
% 4.30/1.78  tff(c_397, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_384])).
% 4.30/1.78  tff(c_355, plain, (r2_hidden('#skF_6', k1_relset_1('#skF_2', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_54])).
% 4.30/1.78  tff(c_399, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_397, c_355])).
% 4.30/1.78  tff(c_495, plain, (![B_128, C_129, A_130]: (k1_funct_1(B_128, C_129)=k1_funct_1(A_130, C_129) | ~r2_hidden(C_129, k1_relat_1(A_130)) | ~r1_partfun1(A_130, B_128) | ~r1_tarski(k1_relat_1(A_130), k1_relat_1(B_128)) | ~v1_funct_1(B_128) | ~v1_relat_1(B_128) | ~v1_funct_1(A_130) | ~v1_relat_1(A_130))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.30/1.78  tff(c_501, plain, (![B_128]: (k1_funct_1(B_128, '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~r1_partfun1('#skF_4', B_128) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_128)) | ~v1_funct_1(B_128) | ~v1_relat_1(B_128) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_399, c_495])).
% 4.30/1.78  tff(c_508, plain, (![B_131]: (k1_funct_1(B_131, '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~r1_partfun1('#skF_4', B_131) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_131)) | ~v1_funct_1(B_131) | ~v1_relat_1(B_131))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_50, c_501])).
% 4.30/1.78  tff(c_511, plain, (k1_funct_1('#skF_5', '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~r1_partfun1('#skF_4', '#skF_5') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_433, c_508])).
% 4.30/1.78  tff(c_516, plain, (k1_funct_1('#skF_5', '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_46, c_356, c_511])).
% 4.30/1.78  tff(c_517, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_359, c_516])).
% 4.30/1.78  tff(c_527, plain, (~v4_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_12, c_517])).
% 4.30/1.78  tff(c_531, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_105, c_133, c_527])).
% 4.30/1.78  tff(c_533, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_40])).
% 4.30/1.78  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.30/1.78  tff(c_551, plain, (![A_136]: (k2_zfmisc_1(A_136, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_533, c_533, c_4])).
% 4.30/1.78  tff(c_555, plain, (v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_551, c_14])).
% 4.30/1.78  tff(c_550, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_533, c_533, c_4])).
% 4.30/1.78  tff(c_532, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_40])).
% 4.30/1.78  tff(c_538, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_533, c_532])).
% 4.30/1.78  tff(c_580, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_550, c_538, c_48])).
% 4.30/1.78  tff(c_581, plain, (![B_138, A_139]: (v1_relat_1(B_138) | ~m1_subset_1(B_138, k1_zfmisc_1(A_139)) | ~v1_relat_1(A_139))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.30/1.78  tff(c_584, plain, (v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_580, c_581])).
% 4.30/1.78  tff(c_590, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_555, c_584])).
% 4.30/1.78  tff(c_1252, plain, (![C_253, A_254, B_255]: (v4_relat_1(C_253, A_254) | ~m1_subset_1(C_253, k1_zfmisc_1(k2_zfmisc_1(A_254, B_255))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.30/1.78  tff(c_1260, plain, (![C_257, A_258]: (v4_relat_1(C_257, A_258) | ~m1_subset_1(C_257, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_550, c_1252])).
% 4.30/1.78  tff(c_1265, plain, (![A_258]: (v4_relat_1('#skF_4', A_258))), inference(resolution, [status(thm)], [c_580, c_1260])).
% 4.30/1.78  tff(c_594, plain, (~r1_partfun1('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_52])).
% 4.30/1.78  tff(c_543, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_538, c_42])).
% 4.30/1.78  tff(c_579, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_550, c_543])).
% 4.30/1.78  tff(c_587, plain, (v1_relat_1('#skF_5') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_579, c_581])).
% 4.30/1.78  tff(c_593, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_555, c_587])).
% 4.30/1.78  tff(c_630, plain, (![C_153, A_154, B_155]: (v4_relat_1(C_153, A_154) | ~m1_subset_1(C_153, k1_zfmisc_1(k2_zfmisc_1(A_154, B_155))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.30/1.78  tff(c_648, plain, (![C_157, A_158]: (v4_relat_1(C_157, A_158) | ~m1_subset_1(C_157, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_550, c_630])).
% 4.30/1.78  tff(c_653, plain, (![A_158]: (v4_relat_1('#skF_4', A_158))), inference(resolution, [status(thm)], [c_580, c_648])).
% 4.30/1.78  tff(c_6, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.30/1.78  tff(c_560, plain, (![B_2]: (k2_zfmisc_1('#skF_3', B_2)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_533, c_533, c_6])).
% 4.30/1.78  tff(c_670, plain, (![A_164, B_165, C_166]: (k1_relset_1(A_164, B_165, C_166)=k1_relat_1(C_166) | ~m1_subset_1(C_166, k1_zfmisc_1(k2_zfmisc_1(A_164, B_165))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.30/1.78  tff(c_677, plain, (![B_167, C_168]: (k1_relset_1('#skF_3', B_167, C_168)=k1_relat_1(C_168) | ~m1_subset_1(C_168, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_560, c_670])).
% 4.30/1.78  tff(c_683, plain, (![B_167]: (k1_relset_1('#skF_3', B_167, '#skF_5')=k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_579, c_677])).
% 4.30/1.78  tff(c_26, plain, (![C_18, B_17]: (v1_funct_2(C_18, k1_xboole_0, B_17) | k1_relset_1(k1_xboole_0, B_17, C_18)!=k1_xboole_0 | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_17))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.30/1.78  tff(c_64, plain, (![C_18, B_17]: (v1_funct_2(C_18, k1_xboole_0, B_17) | k1_relset_1(k1_xboole_0, B_17, C_18)!=k1_xboole_0 | ~m1_subset_1(C_18, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_26])).
% 4.30/1.78  tff(c_685, plain, (![C_169, B_170]: (v1_funct_2(C_169, '#skF_3', B_170) | k1_relset_1('#skF_3', B_170, C_169)!='#skF_3' | ~m1_subset_1(C_169, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_533, c_533, c_533, c_533, c_64])).
% 4.30/1.78  tff(c_691, plain, (![B_170]: (v1_funct_2('#skF_5', '#skF_3', B_170) | k1_relset_1('#skF_3', B_170, '#skF_5')!='#skF_3')), inference(resolution, [status(thm)], [c_579, c_685])).
% 4.30/1.78  tff(c_1041, plain, (![B_170]: (v1_funct_2('#skF_5', '#skF_3', B_170) | k1_relat_1('#skF_5')!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_683, c_691])).
% 4.30/1.78  tff(c_1042, plain, (k1_relat_1('#skF_5')!='#skF_3'), inference(splitLeft, [status(thm)], [c_1041])).
% 4.30/1.78  tff(c_544, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_538, c_44])).
% 4.30/1.78  tff(c_30, plain, (![B_17, C_18]: (k1_relset_1(k1_xboole_0, B_17, C_18)=k1_xboole_0 | ~v1_funct_2(C_18, k1_xboole_0, B_17) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_17))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.30/1.78  tff(c_63, plain, (![B_17, C_18]: (k1_relset_1(k1_xboole_0, B_17, C_18)=k1_xboole_0 | ~v1_funct_2(C_18, k1_xboole_0, B_17) | ~m1_subset_1(C_18, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_30])).
% 4.30/1.78  tff(c_1044, plain, (![B_217, C_218]: (k1_relset_1('#skF_3', B_217, C_218)='#skF_3' | ~v1_funct_2(C_218, '#skF_3', B_217) | ~m1_subset_1(C_218, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_533, c_533, c_533, c_533, c_63])).
% 4.30/1.78  tff(c_1046, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')='#skF_3' | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_544, c_1044])).
% 4.30/1.78  tff(c_1049, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_579, c_683, c_1046])).
% 4.30/1.78  tff(c_1051, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1042, c_1049])).
% 4.30/1.78  tff(c_1053, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_1041])).
% 4.30/1.78  tff(c_1152, plain, (![A_235, B_236]: (r2_hidden('#skF_1'(A_235, B_236), k1_relat_1(A_235)) | r1_partfun1(A_235, B_236) | ~r1_tarski(k1_relat_1(A_235), k1_relat_1(B_236)) | ~v1_funct_1(B_236) | ~v1_relat_1(B_236) | ~v1_funct_1(A_235) | ~v1_relat_1(A_235))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.30/1.78  tff(c_711, plain, (![B_170]: (v1_funct_2('#skF_5', '#skF_3', B_170) | k1_relat_1('#skF_5')!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_683, c_691])).
% 4.30/1.78  tff(c_712, plain, (k1_relat_1('#skF_5')!='#skF_3'), inference(splitLeft, [status(thm)], [c_711])).
% 4.30/1.78  tff(c_721, plain, (![B_175, C_176]: (k1_relset_1('#skF_3', B_175, C_176)='#skF_3' | ~v1_funct_2(C_176, '#skF_3', B_175) | ~m1_subset_1(C_176, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_533, c_533, c_533, c_533, c_63])).
% 4.30/1.78  tff(c_723, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')='#skF_3' | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_544, c_721])).
% 4.30/1.78  tff(c_726, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_579, c_683, c_723])).
% 4.30/1.78  tff(c_728, plain, $false, inference(negUnitSimplification, [status(thm)], [c_712, c_726])).
% 4.30/1.78  tff(c_730, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_711])).
% 4.30/1.78  tff(c_900, plain, (![A_201, B_202]: (r2_hidden('#skF_1'(A_201, B_202), k1_relat_1(A_201)) | r1_partfun1(A_201, B_202) | ~r1_tarski(k1_relat_1(A_201), k1_relat_1(B_202)) | ~v1_funct_1(B_202) | ~v1_relat_1(B_202) | ~v1_funct_1(A_201) | ~v1_relat_1(A_201))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.30/1.78  tff(c_682, plain, (![B_167]: (k1_relset_1('#skF_3', B_167, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_580, c_677])).
% 4.30/1.78  tff(c_58, plain, (![E_36]: (k1_funct_1('#skF_5', '#skF_6')!=k1_funct_1('#skF_4', '#skF_6') | k1_funct_1('#skF_5', E_36)=k1_funct_1('#skF_4', E_36) | ~r2_hidden(E_36, k1_relset_1('#skF_2', '#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.30/1.78  tff(c_756, plain, (![E_36]: (k1_funct_1('#skF_5', '#skF_6')!=k1_funct_1('#skF_4', '#skF_6') | k1_funct_1('#skF_5', E_36)=k1_funct_1('#skF_4', E_36) | ~r2_hidden(E_36, k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_682, c_538, c_58])).
% 4.30/1.78  tff(c_757, plain, (k1_funct_1('#skF_5', '#skF_6')!=k1_funct_1('#skF_4', '#skF_6')), inference(splitLeft, [status(thm)], [c_756])).
% 4.30/1.78  tff(c_60, plain, (![E_36]: (r2_hidden('#skF_6', k1_relset_1('#skF_2', '#skF_3', '#skF_4')) | k1_funct_1('#skF_5', E_36)=k1_funct_1('#skF_4', E_36) | ~r2_hidden(E_36, k1_relset_1('#skF_2', '#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.30/1.78  tff(c_709, plain, (![E_36]: (r2_hidden('#skF_6', k1_relat_1('#skF_4')) | k1_funct_1('#skF_5', E_36)=k1_funct_1('#skF_4', E_36) | ~r2_hidden(E_36, k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_682, c_538, c_682, c_538, c_60])).
% 4.30/1.78  tff(c_710, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_709])).
% 4.30/1.78  tff(c_655, plain, (![E_36]: (r1_partfun1('#skF_4', '#skF_5') | k1_funct_1('#skF_5', E_36)=k1_funct_1('#skF_4', E_36) | ~r2_hidden(E_36, k1_relset_1('#skF_3', '#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_538, c_62])).
% 4.30/1.78  tff(c_656, plain, (![E_36]: (k1_funct_1('#skF_5', E_36)=k1_funct_1('#skF_4', E_36) | ~r2_hidden(E_36, k1_relset_1('#skF_3', '#skF_3', '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_594, c_655])).
% 4.30/1.78  tff(c_810, plain, (![E_186]: (k1_funct_1('#skF_5', E_186)=k1_funct_1('#skF_4', E_186) | ~r2_hidden(E_186, k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_682, c_656])).
% 4.30/1.78  tff(c_813, plain, (k1_funct_1('#skF_5', '#skF_6')=k1_funct_1('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_710, c_810])).
% 4.30/1.78  tff(c_817, plain, $false, inference(negUnitSimplification, [status(thm)], [c_757, c_813])).
% 4.30/1.78  tff(c_818, plain, (![E_36]: (k1_funct_1('#skF_5', E_36)=k1_funct_1('#skF_4', E_36) | ~r2_hidden(E_36, k1_relat_1('#skF_4')))), inference(splitRight, [status(thm)], [c_756])).
% 4.30/1.78  tff(c_904, plain, (![B_202]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_202))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_202)) | r1_partfun1('#skF_4', B_202) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_202)) | ~v1_funct_1(B_202) | ~v1_relat_1(B_202) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_900, c_818])).
% 4.30/1.78  tff(c_914, plain, (![B_204]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_204))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_204)) | r1_partfun1('#skF_4', B_204) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_204)) | ~v1_funct_1(B_204) | ~v1_relat_1(B_204))), inference(demodulation, [status(thm), theory('equality')], [c_590, c_50, c_904])).
% 4.30/1.78  tff(c_917, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_5'))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', '#skF_5')) | r1_partfun1('#skF_4', '#skF_5') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_3') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_730, c_914])).
% 4.30/1.78  tff(c_922, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_5'))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', '#skF_5')) | r1_partfun1('#skF_4', '#skF_5') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_593, c_46, c_917])).
% 4.30/1.78  tff(c_923, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_5'))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', '#skF_5')) | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_594, c_922])).
% 4.30/1.78  tff(c_927, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_923])).
% 4.30/1.78  tff(c_930, plain, (~v4_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_12, c_927])).
% 4.30/1.78  tff(c_934, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_590, c_653, c_930])).
% 4.30/1.78  tff(c_936, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_923])).
% 4.30/1.78  tff(c_920, plain, (![B_204]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_204))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_204)) | r1_partfun1('#skF_4', B_204) | ~v1_funct_1(B_204) | ~v1_relat_1(B_204) | ~v4_relat_1('#skF_4', k1_relat_1(B_204)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_12, c_914])).
% 4.30/1.78  tff(c_926, plain, (![B_204]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_204))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_204)) | r1_partfun1('#skF_4', B_204) | ~v1_funct_1(B_204) | ~v1_relat_1(B_204))), inference(demodulation, [status(thm), theory('equality')], [c_590, c_653, c_920])).
% 4.30/1.78  tff(c_1018, plain, (![B_215, A_216]: (k1_funct_1(B_215, '#skF_1'(A_216, B_215))!=k1_funct_1(A_216, '#skF_1'(A_216, B_215)) | r1_partfun1(A_216, B_215) | ~r1_tarski(k1_relat_1(A_216), k1_relat_1(B_215)) | ~v1_funct_1(B_215) | ~v1_relat_1(B_215) | ~v1_funct_1(A_216) | ~v1_relat_1(A_216))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.30/1.78  tff(c_1026, plain, (~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | r1_partfun1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_926, c_1018])).
% 4.30/1.78  tff(c_1036, plain, (r1_partfun1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_593, c_46, c_590, c_50, c_936, c_730, c_1026])).
% 4.30/1.78  tff(c_1038, plain, $false, inference(negUnitSimplification, [status(thm)], [c_594, c_1036])).
% 4.30/1.78  tff(c_1039, plain, (![E_36]: (k1_funct_1('#skF_5', E_36)=k1_funct_1('#skF_4', E_36) | ~r2_hidden(E_36, k1_relat_1('#skF_4')))), inference(splitRight, [status(thm)], [c_709])).
% 4.30/1.78  tff(c_1156, plain, (![B_236]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_236))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_236)) | r1_partfun1('#skF_4', B_236) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_236)) | ~v1_funct_1(B_236) | ~v1_relat_1(B_236) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_1152, c_1039])).
% 4.30/1.78  tff(c_1166, plain, (![B_238]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_238))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_238)) | r1_partfun1('#skF_4', B_238) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_238)) | ~v1_funct_1(B_238) | ~v1_relat_1(B_238))), inference(demodulation, [status(thm), theory('equality')], [c_590, c_50, c_1156])).
% 4.30/1.78  tff(c_1169, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_5'))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', '#skF_5')) | r1_partfun1('#skF_4', '#skF_5') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_3') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1053, c_1166])).
% 4.30/1.78  tff(c_1174, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_5'))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', '#skF_5')) | r1_partfun1('#skF_4', '#skF_5') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_593, c_46, c_1169])).
% 4.30/1.78  tff(c_1175, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_5'))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', '#skF_5')) | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_594, c_1174])).
% 4.30/1.78  tff(c_1179, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_1175])).
% 4.30/1.78  tff(c_1182, plain, (~v4_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_12, c_1179])).
% 4.30/1.78  tff(c_1186, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_590, c_653, c_1182])).
% 4.30/1.78  tff(c_1188, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_1175])).
% 4.30/1.78  tff(c_1187, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_5'))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_1175])).
% 4.30/1.78  tff(c_36, plain, (![B_25, A_19]: (k1_funct_1(B_25, '#skF_1'(A_19, B_25))!=k1_funct_1(A_19, '#skF_1'(A_19, B_25)) | r1_partfun1(A_19, B_25) | ~r1_tarski(k1_relat_1(A_19), k1_relat_1(B_25)) | ~v1_funct_1(B_25) | ~v1_relat_1(B_25) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.30/1.78  tff(c_1201, plain, (r1_partfun1('#skF_4', '#skF_5') | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1187, c_36])).
% 4.30/1.78  tff(c_1206, plain, (r1_partfun1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_590, c_50, c_593, c_46, c_1188, c_1053, c_1201])).
% 4.30/1.78  tff(c_1208, plain, $false, inference(negUnitSimplification, [status(thm)], [c_594, c_1206])).
% 4.30/1.78  tff(c_1209, plain, (k1_funct_1('#skF_5', '#skF_6')!=k1_funct_1('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_52])).
% 4.30/1.78  tff(c_1210, plain, (r1_partfun1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_52])).
% 4.30/1.78  tff(c_1272, plain, (![A_261, B_262, C_263]: (k1_relset_1(A_261, B_262, C_263)=k1_relat_1(C_263) | ~m1_subset_1(C_263, k1_zfmisc_1(k2_zfmisc_1(A_261, B_262))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.30/1.78  tff(c_1279, plain, (![B_264, C_265]: (k1_relset_1('#skF_3', B_264, C_265)=k1_relat_1(C_265) | ~m1_subset_1(C_265, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_560, c_1272])).
% 4.30/1.78  tff(c_1285, plain, (![B_264]: (k1_relset_1('#skF_3', B_264, '#skF_5')=k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_579, c_1279])).
% 4.30/1.78  tff(c_1348, plain, (![C_274, B_275]: (v1_funct_2(C_274, '#skF_3', B_275) | k1_relset_1('#skF_3', B_275, C_274)!='#skF_3' | ~m1_subset_1(C_274, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_533, c_533, c_533, c_533, c_64])).
% 4.30/1.78  tff(c_1352, plain, (![B_275]: (v1_funct_2('#skF_5', '#skF_3', B_275) | k1_relset_1('#skF_3', B_275, '#skF_5')!='#skF_3')), inference(resolution, [status(thm)], [c_579, c_1348])).
% 4.30/1.78  tff(c_1356, plain, (![B_275]: (v1_funct_2('#skF_5', '#skF_3', B_275) | k1_relat_1('#skF_5')!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1285, c_1352])).
% 4.30/1.78  tff(c_1358, plain, (k1_relat_1('#skF_5')!='#skF_3'), inference(splitLeft, [status(thm)], [c_1356])).
% 4.30/1.78  tff(c_1360, plain, (![B_276, C_277]: (k1_relset_1('#skF_3', B_276, C_277)='#skF_3' | ~v1_funct_2(C_277, '#skF_3', B_276) | ~m1_subset_1(C_277, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_533, c_533, c_533, c_533, c_63])).
% 4.30/1.78  tff(c_1362, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')='#skF_3' | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_544, c_1360])).
% 4.30/1.78  tff(c_1365, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_579, c_1285, c_1362])).
% 4.30/1.78  tff(c_1367, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1358, c_1365])).
% 4.30/1.78  tff(c_1369, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_1356])).
% 4.30/1.78  tff(c_1284, plain, (![B_264]: (k1_relset_1('#skF_3', B_264, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_580, c_1279])).
% 4.30/1.78  tff(c_1211, plain, (r2_hidden('#skF_6', k1_relset_1('#skF_3', '#skF_3', '#skF_4')) | ~r1_partfun1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_538, c_54])).
% 4.30/1.78  tff(c_1212, plain, (~r1_partfun1('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_1211])).
% 4.30/1.78  tff(c_1214, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1210, c_1212])).
% 4.30/1.78  tff(c_1215, plain, (r2_hidden('#skF_6', k1_relset_1('#skF_3', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_1211])).
% 4.30/1.78  tff(c_1286, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1284, c_1215])).
% 4.30/1.78  tff(c_1471, plain, (![B_296, C_297, A_298]: (k1_funct_1(B_296, C_297)=k1_funct_1(A_298, C_297) | ~r2_hidden(C_297, k1_relat_1(A_298)) | ~r1_partfun1(A_298, B_296) | ~r1_tarski(k1_relat_1(A_298), k1_relat_1(B_296)) | ~v1_funct_1(B_296) | ~v1_relat_1(B_296) | ~v1_funct_1(A_298) | ~v1_relat_1(A_298))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.30/1.78  tff(c_1477, plain, (![B_296]: (k1_funct_1(B_296, '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~r1_partfun1('#skF_4', B_296) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_296)) | ~v1_funct_1(B_296) | ~v1_relat_1(B_296) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_1286, c_1471])).
% 4.30/1.78  tff(c_1508, plain, (![B_302]: (k1_funct_1(B_302, '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~r1_partfun1('#skF_4', B_302) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_302)) | ~v1_funct_1(B_302) | ~v1_relat_1(B_302))), inference(demodulation, [status(thm), theory('equality')], [c_590, c_50, c_1477])).
% 4.30/1.78  tff(c_1511, plain, (k1_funct_1('#skF_5', '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~r1_partfun1('#skF_4', '#skF_5') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_3') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1369, c_1508])).
% 4.30/1.78  tff(c_1516, plain, (k1_funct_1('#skF_5', '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_593, c_46, c_1210, c_1511])).
% 4.30/1.78  tff(c_1517, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_1209, c_1516])).
% 4.30/1.78  tff(c_1523, plain, (~v4_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_12, c_1517])).
% 4.30/1.78  tff(c_1527, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_590, c_1265, c_1523])).
% 4.30/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.30/1.78  
% 4.30/1.78  Inference rules
% 4.30/1.78  ----------------------
% 4.30/1.78  #Ref     : 5
% 4.30/1.78  #Sup     : 300
% 4.30/1.78  #Fact    : 0
% 4.30/1.78  #Define  : 0
% 4.30/1.78  #Split   : 22
% 4.30/1.78  #Chain   : 0
% 4.30/1.78  #Close   : 0
% 4.30/1.78  
% 4.30/1.78  Ordering : KBO
% 4.30/1.78  
% 4.30/1.78  Simplification rules
% 4.30/1.78  ----------------------
% 4.30/1.78  #Subsume      : 28
% 4.30/1.78  #Demod        : 331
% 4.30/1.78  #Tautology    : 165
% 4.30/1.78  #SimpNegUnit  : 26
% 4.30/1.78  #BackRed      : 13
% 4.30/1.78  
% 4.30/1.78  #Partial instantiations: 0
% 4.30/1.78  #Strategies tried      : 1
% 4.30/1.78  
% 4.30/1.78  Timing (in seconds)
% 4.30/1.78  ----------------------
% 4.30/1.78  Preprocessing        : 0.35
% 4.30/1.78  Parsing              : 0.19
% 4.30/1.78  CNF conversion       : 0.03
% 4.30/1.78  Main loop            : 0.61
% 4.30/1.78  Inferencing          : 0.23
% 4.30/1.78  Reduction            : 0.20
% 4.30/1.78  Demodulation         : 0.14
% 4.30/1.78  BG Simplification    : 0.03
% 4.30/1.78  Subsumption          : 0.10
% 4.30/1.78  Abstraction          : 0.03
% 4.30/1.78  MUC search           : 0.00
% 4.30/1.78  Cooper               : 0.00
% 4.30/1.78  Total                : 1.04
% 4.30/1.78  Index Insertion      : 0.00
% 4.30/1.78  Index Deletion       : 0.00
% 4.30/1.78  Index Matching       : 0.00
% 4.30/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
