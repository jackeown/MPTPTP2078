%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:52 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 535 expanded)
%              Number of leaves         :   33 ( 198 expanded)
%              Depth                    :   13
%              Number of atoms          :  164 (1262 expanded)
%              Number of equality atoms :   32 ( 408 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_4 > #skF_2

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_123,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( r1_partfun1(C,D)
             => ( ( B = k1_xboole_0
                  & A != k1_xboole_0 )
                | r2_relset_1(A,B,C,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_2)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_31,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ( v1_partfun1(C,A)
              & v1_partfun1(D,A)
              & r1_partfun1(C,D) )
           => C = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_83,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_partfun1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(c_42,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_220,plain,(
    ! [A_66,B_67,C_68,D_69] :
      ( r2_relset_1(A_66,B_67,C_68,C_68)
      | ~ m1_subset_1(D_69,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67)))
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_259,plain,(
    ! [C_73] :
      ( r2_relset_1('#skF_3','#skF_4',C_73,C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_48,c_220])).

tff(c_272,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_259])).

tff(c_4,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_53,plain,(
    ! [A_29] :
      ( k1_xboole_0 = A_29
      | ~ v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_57,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_53])).

tff(c_38,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_66,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_1' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_57,c_38])).

tff(c_67,plain,(
    '#skF_1' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_52,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_50,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_175,plain,(
    ! [C_63,A_64,B_65] :
      ( v1_partfun1(C_63,A_64)
      | ~ v1_funct_2(C_63,A_64,B_65)
      | ~ v1_funct_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65)))
      | v1_xboole_0(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_181,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_175])).

tff(c_200,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_181])).

tff(c_206,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_200])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_60,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_2])).

tff(c_209,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_206,c_60])).

tff(c_213,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_209])).

tff(c_214,plain,(
    v1_partfun1('#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_200])).

tff(c_215,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_200])).

tff(c_46,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_44,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_184,plain,
    ( v1_partfun1('#skF_6','#skF_3')
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_175])).

tff(c_203,plain,
    ( v1_partfun1('#skF_6','#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_184])).

tff(c_216,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_203])).

tff(c_217,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_215,c_216])).

tff(c_218,plain,(
    v1_partfun1('#skF_6','#skF_3') ),
    inference(splitRight,[status(thm)],[c_203])).

tff(c_40,plain,(
    r1_partfun1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_326,plain,(
    ! [D_77,C_78,A_79,B_80] :
      ( D_77 = C_78
      | ~ r1_partfun1(C_78,D_77)
      | ~ v1_partfun1(D_77,A_79)
      | ~ v1_partfun1(C_78,A_79)
      | ~ m1_subset_1(D_77,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80)))
      | ~ v1_funct_1(D_77)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80)))
      | ~ v1_funct_1(C_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_328,plain,(
    ! [A_79,B_80] :
      ( '#skF_5' = '#skF_6'
      | ~ v1_partfun1('#skF_6',A_79)
      | ~ v1_partfun1('#skF_5',A_79)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_79,B_80)))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_79,B_80)))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40,c_326])).

tff(c_331,plain,(
    ! [A_79,B_80] :
      ( '#skF_5' = '#skF_6'
      | ~ v1_partfun1('#skF_6',A_79)
      | ~ v1_partfun1('#skF_5',A_79)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_79,B_80)))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_328])).

tff(c_598,plain,(
    ! [A_115,B_116] :
      ( ~ v1_partfun1('#skF_6',A_115)
      | ~ v1_partfun1('#skF_5',A_115)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_115,B_116)))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_115,B_116))) ) ),
    inference(splitLeft,[status(thm)],[c_331])).

tff(c_601,plain,
    ( ~ v1_partfun1('#skF_6','#skF_3')
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_48,c_598])).

tff(c_611,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_214,c_218,c_601])).

tff(c_612,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_331])).

tff(c_36,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_617,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_612,c_36])).

tff(c_626,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_617])).

tff(c_628,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_12,plain,(
    ! [A_4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_59,plain,(
    ! [A_4] : m1_subset_1('#skF_1',k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_12])).

tff(c_683,plain,(
    ! [A_4] : m1_subset_1('#skF_4',k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_628,c_59])).

tff(c_32,plain,(
    ! [A_20,B_21] : m1_subset_1('#skF_2'(A_20,B_21),k1_zfmisc_1(k2_zfmisc_1(A_20,B_21))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_893,plain,(
    ! [A_157,B_158,C_159,D_160] :
      ( r2_relset_1(A_157,B_158,C_159,C_159)
      | ~ m1_subset_1(D_160,k1_zfmisc_1(k2_zfmisc_1(A_157,B_158)))
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(A_157,B_158))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1038,plain,(
    ! [A_177,B_178,C_179] :
      ( r2_relset_1(A_177,B_178,C_179,C_179)
      | ~ m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1(A_177,B_178))) ) ),
    inference(resolution,[status(thm)],[c_32,c_893])).

tff(c_1049,plain,(
    ! [A_177,B_178] : r2_relset_1(A_177,B_178,'#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_683,c_1038])).

tff(c_635,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_628,c_57])).

tff(c_8,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_650,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_635,c_635,c_8])).

tff(c_627,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_634,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_628,c_627])).

tff(c_688,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_650,c_634,c_48])).

tff(c_636,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_628,c_4])).

tff(c_10,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_658,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_4',B_3) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_635,c_635,c_10])).

tff(c_735,plain,(
    ! [C_144,A_145,B_146] :
      ( v1_xboole_0(C_144)
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(A_145,B_146)))
      | ~ v1_xboole_0(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_745,plain,(
    ! [C_144] :
      ( v1_xboole_0(C_144)
      | ~ m1_subset_1(C_144,k1_zfmisc_1('#skF_4'))
      | ~ v1_xboole_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_658,c_735])).

tff(c_759,plain,(
    ! [C_149] :
      ( v1_xboole_0(C_149)
      | ~ m1_subset_1(C_149,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_636,c_745])).

tff(c_779,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_688,c_759])).

tff(c_676,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_628,c_60])).

tff(c_789,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_779,c_676])).

tff(c_689,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_650,c_634,c_42])).

tff(c_778,plain,(
    v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_689,c_759])).

tff(c_785,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_778,c_676])).

tff(c_685,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_634,c_36])).

tff(c_794,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_785,c_685])).

tff(c_847,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_789,c_794])).

tff(c_1064,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1049,c_847])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:20:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.80/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.44  
% 2.80/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.45  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_4 > #skF_2
% 2.80/1.45  
% 2.80/1.45  %Foreground sorts:
% 2.80/1.45  
% 2.80/1.45  
% 2.80/1.45  %Background operators:
% 2.80/1.45  
% 2.80/1.45  
% 2.80/1.45  %Foreground operators:
% 2.80/1.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.80/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.80/1.45  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.80/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.80/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.80/1.45  tff('#skF_5', type, '#skF_5': $i).
% 2.80/1.45  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.80/1.45  tff('#skF_6', type, '#skF_6': $i).
% 2.80/1.45  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.80/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.80/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.80/1.45  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.80/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.80/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.80/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.80/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.80/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.80/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.80/1.45  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.80/1.45  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.80/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.80/1.45  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 2.80/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.80/1.45  
% 3.18/1.47  tff(f_123, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_relset_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_2)).
% 3.18/1.47  tff(f_58, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 3.18/1.47  tff(f_31, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_xboole_0)).
% 3.18/1.47  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.18/1.47  tff(f_72, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 3.18/1.47  tff(f_100, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_partfun1)).
% 3.18/1.47  tff(f_39, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.18/1.47  tff(f_83, axiom, (![A, B]: (?[C]: ((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_partfun1)).
% 3.18/1.47  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.18/1.47  tff(f_52, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 3.18/1.47  tff(c_42, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.18/1.47  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.18/1.47  tff(c_220, plain, (![A_66, B_67, C_68, D_69]: (r2_relset_1(A_66, B_67, C_68, C_68) | ~m1_subset_1(D_69, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.18/1.47  tff(c_259, plain, (![C_73]: (r2_relset_1('#skF_3', '#skF_4', C_73, C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))))), inference(resolution, [status(thm)], [c_48, c_220])).
% 3.18/1.47  tff(c_272, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_42, c_259])).
% 3.18/1.47  tff(c_4, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.18/1.47  tff(c_53, plain, (![A_29]: (k1_xboole_0=A_29 | ~v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.18/1.47  tff(c_57, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_4, c_53])).
% 3.18/1.47  tff(c_38, plain, (k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.18/1.47  tff(c_66, plain, ('#skF_3'='#skF_1' | '#skF_1'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_57, c_57, c_38])).
% 3.18/1.47  tff(c_67, plain, ('#skF_1'!='#skF_4'), inference(splitLeft, [status(thm)], [c_66])).
% 3.18/1.47  tff(c_52, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.18/1.47  tff(c_50, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.18/1.47  tff(c_175, plain, (![C_63, A_64, B_65]: (v1_partfun1(C_63, A_64) | ~v1_funct_2(C_63, A_64, B_65) | ~v1_funct_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))) | v1_xboole_0(B_65))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.18/1.47  tff(c_181, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_48, c_175])).
% 3.18/1.47  tff(c_200, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_181])).
% 3.18/1.47  tff(c_206, plain, (v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_200])).
% 3.18/1.47  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.18/1.47  tff(c_60, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_2])).
% 3.18/1.47  tff(c_209, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_206, c_60])).
% 3.18/1.47  tff(c_213, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67, c_209])).
% 3.18/1.47  tff(c_214, plain, (v1_partfun1('#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_200])).
% 3.18/1.47  tff(c_215, plain, (~v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_200])).
% 3.18/1.47  tff(c_46, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.18/1.47  tff(c_44, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.18/1.47  tff(c_184, plain, (v1_partfun1('#skF_6', '#skF_3') | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_42, c_175])).
% 3.18/1.47  tff(c_203, plain, (v1_partfun1('#skF_6', '#skF_3') | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_184])).
% 3.18/1.47  tff(c_216, plain, (v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_203])).
% 3.18/1.47  tff(c_217, plain, $false, inference(negUnitSimplification, [status(thm)], [c_215, c_216])).
% 3.18/1.47  tff(c_218, plain, (v1_partfun1('#skF_6', '#skF_3')), inference(splitRight, [status(thm)], [c_203])).
% 3.18/1.47  tff(c_40, plain, (r1_partfun1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.18/1.47  tff(c_326, plain, (![D_77, C_78, A_79, B_80]: (D_77=C_78 | ~r1_partfun1(C_78, D_77) | ~v1_partfun1(D_77, A_79) | ~v1_partfun1(C_78, A_79) | ~m1_subset_1(D_77, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))) | ~v1_funct_1(D_77) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))) | ~v1_funct_1(C_78))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.18/1.47  tff(c_328, plain, (![A_79, B_80]: ('#skF_5'='#skF_6' | ~v1_partfun1('#skF_6', A_79) | ~v1_partfun1('#skF_5', A_79) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_326])).
% 3.18/1.47  tff(c_331, plain, (![A_79, B_80]: ('#skF_5'='#skF_6' | ~v1_partfun1('#skF_6', A_79) | ~v1_partfun1('#skF_5', A_79) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_46, c_328])).
% 3.18/1.47  tff(c_598, plain, (![A_115, B_116]: (~v1_partfun1('#skF_6', A_115) | ~v1_partfun1('#skF_5', A_115) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))))), inference(splitLeft, [status(thm)], [c_331])).
% 3.18/1.47  tff(c_601, plain, (~v1_partfun1('#skF_6', '#skF_3') | ~v1_partfun1('#skF_5', '#skF_3') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_48, c_598])).
% 3.18/1.47  tff(c_611, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_214, c_218, c_601])).
% 3.18/1.47  tff(c_612, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_331])).
% 3.18/1.47  tff(c_36, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.18/1.47  tff(c_617, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_612, c_36])).
% 3.18/1.47  tff(c_626, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_272, c_617])).
% 3.18/1.47  tff(c_628, plain, ('#skF_1'='#skF_4'), inference(splitRight, [status(thm)], [c_66])).
% 3.18/1.47  tff(c_12, plain, (![A_4]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.18/1.47  tff(c_59, plain, (![A_4]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_12])).
% 3.18/1.47  tff(c_683, plain, (![A_4]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_628, c_59])).
% 3.18/1.47  tff(c_32, plain, (![A_20, B_21]: (m1_subset_1('#skF_2'(A_20, B_21), k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.18/1.47  tff(c_893, plain, (![A_157, B_158, C_159, D_160]: (r2_relset_1(A_157, B_158, C_159, C_159) | ~m1_subset_1(D_160, k1_zfmisc_1(k2_zfmisc_1(A_157, B_158))) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(A_157, B_158))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.18/1.47  tff(c_1038, plain, (![A_177, B_178, C_179]: (r2_relset_1(A_177, B_178, C_179, C_179) | ~m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1(A_177, B_178))))), inference(resolution, [status(thm)], [c_32, c_893])).
% 3.18/1.47  tff(c_1049, plain, (![A_177, B_178]: (r2_relset_1(A_177, B_178, '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_683, c_1038])).
% 3.18/1.47  tff(c_635, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_628, c_57])).
% 3.18/1.47  tff(c_8, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.18/1.47  tff(c_650, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_635, c_635, c_8])).
% 3.18/1.47  tff(c_627, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_66])).
% 3.18/1.47  tff(c_634, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_628, c_627])).
% 3.18/1.47  tff(c_688, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_650, c_634, c_48])).
% 3.18/1.47  tff(c_636, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_628, c_4])).
% 3.18/1.47  tff(c_10, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.18/1.47  tff(c_658, plain, (![B_3]: (k2_zfmisc_1('#skF_4', B_3)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_635, c_635, c_10])).
% 3.18/1.47  tff(c_735, plain, (![C_144, A_145, B_146]: (v1_xboole_0(C_144) | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(A_145, B_146))) | ~v1_xboole_0(A_145))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.18/1.47  tff(c_745, plain, (![C_144]: (v1_xboole_0(C_144) | ~m1_subset_1(C_144, k1_zfmisc_1('#skF_4')) | ~v1_xboole_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_658, c_735])).
% 3.18/1.47  tff(c_759, plain, (![C_149]: (v1_xboole_0(C_149) | ~m1_subset_1(C_149, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_636, c_745])).
% 3.18/1.47  tff(c_779, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_688, c_759])).
% 3.18/1.47  tff(c_676, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_628, c_60])).
% 3.18/1.47  tff(c_789, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_779, c_676])).
% 3.18/1.47  tff(c_689, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_650, c_634, c_42])).
% 3.18/1.47  tff(c_778, plain, (v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_689, c_759])).
% 3.18/1.47  tff(c_785, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_778, c_676])).
% 3.18/1.47  tff(c_685, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_634, c_36])).
% 3.18/1.47  tff(c_794, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_785, c_685])).
% 3.18/1.47  tff(c_847, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_789, c_794])).
% 3.18/1.47  tff(c_1064, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1049, c_847])).
% 3.18/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/1.47  
% 3.18/1.47  Inference rules
% 3.18/1.47  ----------------------
% 3.18/1.47  #Ref     : 0
% 3.18/1.47  #Sup     : 226
% 3.18/1.47  #Fact    : 0
% 3.18/1.47  #Define  : 0
% 3.18/1.47  #Split   : 6
% 3.18/1.47  #Chain   : 0
% 3.18/1.47  #Close   : 0
% 3.18/1.47  
% 3.18/1.47  Ordering : KBO
% 3.18/1.47  
% 3.18/1.47  Simplification rules
% 3.18/1.47  ----------------------
% 3.18/1.47  #Subsume      : 27
% 3.18/1.47  #Demod        : 222
% 3.18/1.47  #Tautology    : 147
% 3.18/1.47  #SimpNegUnit  : 2
% 3.18/1.47  #BackRed      : 40
% 3.18/1.47  
% 3.18/1.47  #Partial instantiations: 0
% 3.18/1.47  #Strategies tried      : 1
% 3.18/1.47  
% 3.18/1.47  Timing (in seconds)
% 3.18/1.47  ----------------------
% 3.18/1.47  Preprocessing        : 0.31
% 3.18/1.47  Parsing              : 0.17
% 3.18/1.47  CNF conversion       : 0.02
% 3.18/1.47  Main loop            : 0.39
% 3.18/1.47  Inferencing          : 0.14
% 3.18/1.47  Reduction            : 0.13
% 3.18/1.47  Demodulation         : 0.09
% 3.18/1.47  BG Simplification    : 0.02
% 3.18/1.47  Subsumption          : 0.06
% 3.18/1.47  Abstraction          : 0.01
% 3.18/1.47  MUC search           : 0.00
% 3.18/1.47  Cooper               : 0.00
% 3.18/1.47  Total                : 0.74
% 3.18/1.47  Index Insertion      : 0.00
% 3.18/1.47  Index Deletion       : 0.00
% 3.18/1.47  Index Matching       : 0.00
% 3.18/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
