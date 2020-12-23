%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:52 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 600 expanded)
%              Number of leaves         :   23 ( 190 expanded)
%              Depth                    :   11
%              Number of atoms          :  186 (2135 expanded)
%              Number of equality atoms :   25 ( 573 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,negated_conjecture,(
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

tff(f_44,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_75,axiom,(
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

tff(f_36,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(c_22,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_45,plain,(
    ! [A_24,B_25,D_26] :
      ( r2_relset_1(A_24,B_25,D_26,D_26)
      | ~ m1_subset_1(D_26,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_51,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_45])).

tff(c_18,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_33,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_32,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_30,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_52,plain,(
    ! [C_27,A_28,B_29] :
      ( v1_partfun1(C_27,A_28)
      | ~ v1_funct_2(C_27,A_28,B_29)
      | ~ v1_funct_1(C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29)))
      | v1_xboole_0(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_55,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_52])).

tff(c_61,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_55])).

tff(c_65,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_61])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_68,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_65,c_2])).

tff(c_72,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33,c_68])).

tff(c_73,plain,(
    v1_partfun1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_61])).

tff(c_74,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_61])).

tff(c_26,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_24,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_58,plain,
    ( v1_partfun1('#skF_4','#skF_1')
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_52])).

tff(c_64,plain,
    ( v1_partfun1('#skF_4','#skF_1')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_58])).

tff(c_75,plain,(
    v1_partfun1('#skF_4','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_64])).

tff(c_20,plain,(
    r1_partfun1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_89,plain,(
    ! [D_34,C_35,A_36,B_37] :
      ( D_34 = C_35
      | ~ r1_partfun1(C_35,D_34)
      | ~ v1_partfun1(D_34,A_36)
      | ~ v1_partfun1(C_35,A_36)
      | ~ m1_subset_1(D_34,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37)))
      | ~ v1_funct_1(D_34)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37)))
      | ~ v1_funct_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_91,plain,(
    ! [A_36,B_37] :
      ( '#skF_3' = '#skF_4'
      | ~ v1_partfun1('#skF_4',A_36)
      | ~ v1_partfun1('#skF_3',A_36)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_36,B_37)))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_36,B_37)))
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_89])).

tff(c_94,plain,(
    ! [A_36,B_37] :
      ( '#skF_3' = '#skF_4'
      | ~ v1_partfun1('#skF_4',A_36)
      | ~ v1_partfun1('#skF_3',A_36)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_36,B_37)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_26,c_91])).

tff(c_96,plain,(
    ! [A_38,B_39] :
      ( ~ v1_partfun1('#skF_4',A_38)
      | ~ v1_partfun1('#skF_3',A_38)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_38,B_39)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_99,plain,
    ( ~ v1_partfun1('#skF_4','#skF_1')
    | ~ v1_partfun1('#skF_3','#skF_1')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_28,c_96])).

tff(c_103,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_73,c_75,c_99])).

tff(c_104,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_16,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_108,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_16])).

tff(c_117,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_108])).

tff(c_118,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_119,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_124,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_119])).

tff(c_135,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_22])).

tff(c_146,plain,(
    ! [A_44,B_45,D_46] :
      ( r2_relset_1(A_44,B_45,D_46,D_46)
      | ~ m1_subset_1(D_46,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_151,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_135,c_146])).

tff(c_136,plain,(
    ! [C_41,A_42,B_43] :
      ( v1_xboole_0(C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43)))
      | ~ v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_143,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_135,c_136])).

tff(c_145,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_143])).

tff(c_126,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_30])).

tff(c_134,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_28])).

tff(c_153,plain,(
    ! [C_47,A_48,B_49] :
      ( v1_partfun1(C_47,A_48)
      | ~ v1_funct_2(C_47,A_48,B_49)
      | ~ v1_funct_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49)))
      | v1_xboole_0(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_159,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_134,c_153])).

tff(c_166,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_126,c_159])).

tff(c_167,plain,(
    v1_partfun1('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_145,c_166])).

tff(c_125,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_24])).

tff(c_156,plain,
    ( v1_partfun1('#skF_4','#skF_1')
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_135,c_153])).

tff(c_162,plain,
    ( v1_partfun1('#skF_4','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_125,c_156])).

tff(c_163,plain,(
    v1_partfun1('#skF_4','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_145,c_162])).

tff(c_181,plain,(
    ! [D_54,C_55,A_56,B_57] :
      ( D_54 = C_55
      | ~ r1_partfun1(C_55,D_54)
      | ~ v1_partfun1(D_54,A_56)
      | ~ v1_partfun1(C_55,A_56)
      | ~ m1_subset_1(D_54,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57)))
      | ~ v1_funct_1(D_54)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57)))
      | ~ v1_funct_1(C_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_183,plain,(
    ! [A_56,B_57] :
      ( '#skF_3' = '#skF_4'
      | ~ v1_partfun1('#skF_4',A_56)
      | ~ v1_partfun1('#skF_3',A_56)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_56,B_57)))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_56,B_57)))
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_181])).

tff(c_186,plain,(
    ! [A_56,B_57] :
      ( '#skF_3' = '#skF_4'
      | ~ v1_partfun1('#skF_4',A_56)
      | ~ v1_partfun1('#skF_3',A_56)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_56,B_57)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_26,c_183])).

tff(c_188,plain,(
    ! [A_58,B_59] :
      ( ~ v1_partfun1('#skF_4',A_58)
      | ~ v1_partfun1('#skF_3',A_58)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_58,B_59)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(splitLeft,[status(thm)],[c_186])).

tff(c_191,plain,
    ( ~ v1_partfun1('#skF_4','#skF_1')
    | ~ v1_partfun1('#skF_3','#skF_1')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_134,c_188])).

tff(c_195,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_167,c_163,c_191])).

tff(c_196,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_133,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_16])).

tff(c_200,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_133])).

tff(c_209,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_200])).

tff(c_210,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_143])).

tff(c_131,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_2])).

tff(c_215,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_210,c_131])).

tff(c_144,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_134,c_136])).

tff(c_251,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_215,c_144])).

tff(c_252,plain,(
    ! [A_63] :
      ( A_63 = '#skF_4'
      | ~ v1_xboole_0(A_63) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_131])).

tff(c_259,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_251,c_252])).

tff(c_221,plain,(
    ! [A_60,B_61,D_62] :
      ( r2_relset_1(A_60,B_61,D_62,D_62)
      | ~ m1_subset_1(D_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_227,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_134,c_221])).

tff(c_273,plain,(
    r2_relset_1('#skF_4','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_259,c_215,c_215,c_227])).

tff(c_231,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_215,c_133])).

tff(c_276,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_273,c_259,c_231])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:21:38 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.28  
% 2.14/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.28  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.14/1.28  
% 2.14/1.28  %Foreground sorts:
% 2.14/1.28  
% 2.14/1.28  
% 2.14/1.28  %Background operators:
% 2.14/1.28  
% 2.14/1.28  
% 2.14/1.28  %Foreground operators:
% 2.14/1.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.14/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.28  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.14/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.14/1.28  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.14/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.14/1.28  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.14/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.14/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.14/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.14/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.14/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.14/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.14/1.28  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 2.14/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.14/1.28  
% 2.14/1.30  tff(f_98, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_relset_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_2)).
% 2.14/1.30  tff(f_44, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.14/1.30  tff(f_58, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.14/1.30  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.14/1.30  tff(f_75, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_partfun1)).
% 2.14/1.30  tff(f_36, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 2.14/1.30  tff(c_22, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.14/1.30  tff(c_45, plain, (![A_24, B_25, D_26]: (r2_relset_1(A_24, B_25, D_26, D_26) | ~m1_subset_1(D_26, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.14/1.30  tff(c_51, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_22, c_45])).
% 2.14/1.30  tff(c_18, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.14/1.30  tff(c_33, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_18])).
% 2.14/1.30  tff(c_32, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.14/1.30  tff(c_30, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.14/1.30  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.14/1.30  tff(c_52, plain, (![C_27, A_28, B_29]: (v1_partfun1(C_27, A_28) | ~v1_funct_2(C_27, A_28, B_29) | ~v1_funct_1(C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))) | v1_xboole_0(B_29))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.14/1.30  tff(c_55, plain, (v1_partfun1('#skF_3', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_28, c_52])).
% 2.14/1.30  tff(c_61, plain, (v1_partfun1('#skF_3', '#skF_1') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_55])).
% 2.14/1.30  tff(c_65, plain, (v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_61])).
% 2.14/1.30  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.14/1.30  tff(c_68, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_65, c_2])).
% 2.14/1.30  tff(c_72, plain, $false, inference(negUnitSimplification, [status(thm)], [c_33, c_68])).
% 2.14/1.30  tff(c_73, plain, (v1_partfun1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_61])).
% 2.14/1.30  tff(c_74, plain, (~v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_61])).
% 2.14/1.30  tff(c_26, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.14/1.30  tff(c_24, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.14/1.30  tff(c_58, plain, (v1_partfun1('#skF_4', '#skF_1') | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_22, c_52])).
% 2.14/1.30  tff(c_64, plain, (v1_partfun1('#skF_4', '#skF_1') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_58])).
% 2.14/1.30  tff(c_75, plain, (v1_partfun1('#skF_4', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_74, c_64])).
% 2.14/1.30  tff(c_20, plain, (r1_partfun1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.14/1.30  tff(c_89, plain, (![D_34, C_35, A_36, B_37]: (D_34=C_35 | ~r1_partfun1(C_35, D_34) | ~v1_partfun1(D_34, A_36) | ~v1_partfun1(C_35, A_36) | ~m1_subset_1(D_34, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))) | ~v1_funct_1(D_34) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))) | ~v1_funct_1(C_35))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.14/1.30  tff(c_91, plain, (![A_36, B_37]: ('#skF_3'='#skF_4' | ~v1_partfun1('#skF_4', A_36) | ~v1_partfun1('#skF_3', A_36) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_20, c_89])).
% 2.14/1.30  tff(c_94, plain, (![A_36, B_37]: ('#skF_3'='#skF_4' | ~v1_partfun1('#skF_4', A_36) | ~v1_partfun1('#skF_3', A_36) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_26, c_91])).
% 2.14/1.30  tff(c_96, plain, (![A_38, B_39]: (~v1_partfun1('#skF_4', A_38) | ~v1_partfun1('#skF_3', A_38) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(splitLeft, [status(thm)], [c_94])).
% 2.14/1.30  tff(c_99, plain, (~v1_partfun1('#skF_4', '#skF_1') | ~v1_partfun1('#skF_3', '#skF_1') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_28, c_96])).
% 2.14/1.30  tff(c_103, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_73, c_75, c_99])).
% 2.14/1.30  tff(c_104, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_94])).
% 2.14/1.30  tff(c_16, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.14/1.30  tff(c_108, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_16])).
% 2.14/1.30  tff(c_117, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_51, c_108])).
% 2.14/1.30  tff(c_118, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_18])).
% 2.14/1.30  tff(c_119, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_18])).
% 2.14/1.30  tff(c_124, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_118, c_119])).
% 2.14/1.30  tff(c_135, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_22])).
% 2.14/1.30  tff(c_146, plain, (![A_44, B_45, D_46]: (r2_relset_1(A_44, B_45, D_46, D_46) | ~m1_subset_1(D_46, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.14/1.30  tff(c_151, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_135, c_146])).
% 2.14/1.30  tff(c_136, plain, (![C_41, A_42, B_43]: (v1_xboole_0(C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))) | ~v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.14/1.30  tff(c_143, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_135, c_136])).
% 2.14/1.30  tff(c_145, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_143])).
% 2.14/1.30  tff(c_126, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_30])).
% 2.14/1.30  tff(c_134, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_28])).
% 2.14/1.30  tff(c_153, plain, (![C_47, A_48, B_49]: (v1_partfun1(C_47, A_48) | ~v1_funct_2(C_47, A_48, B_49) | ~v1_funct_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))) | v1_xboole_0(B_49))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.14/1.30  tff(c_159, plain, (v1_partfun1('#skF_3', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_134, c_153])).
% 2.14/1.30  tff(c_166, plain, (v1_partfun1('#skF_3', '#skF_1') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_126, c_159])).
% 2.14/1.30  tff(c_167, plain, (v1_partfun1('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_145, c_166])).
% 2.14/1.30  tff(c_125, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_24])).
% 2.14/1.30  tff(c_156, plain, (v1_partfun1('#skF_4', '#skF_1') | ~v1_funct_2('#skF_4', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_135, c_153])).
% 2.14/1.30  tff(c_162, plain, (v1_partfun1('#skF_4', '#skF_1') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_125, c_156])).
% 2.14/1.30  tff(c_163, plain, (v1_partfun1('#skF_4', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_145, c_162])).
% 2.14/1.30  tff(c_181, plain, (![D_54, C_55, A_56, B_57]: (D_54=C_55 | ~r1_partfun1(C_55, D_54) | ~v1_partfun1(D_54, A_56) | ~v1_partfun1(C_55, A_56) | ~m1_subset_1(D_54, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))) | ~v1_funct_1(D_54) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))) | ~v1_funct_1(C_55))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.14/1.30  tff(c_183, plain, (![A_56, B_57]: ('#skF_3'='#skF_4' | ~v1_partfun1('#skF_4', A_56) | ~v1_partfun1('#skF_3', A_56) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_20, c_181])).
% 2.14/1.30  tff(c_186, plain, (![A_56, B_57]: ('#skF_3'='#skF_4' | ~v1_partfun1('#skF_4', A_56) | ~v1_partfun1('#skF_3', A_56) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_26, c_183])).
% 2.14/1.30  tff(c_188, plain, (![A_58, B_59]: (~v1_partfun1('#skF_4', A_58) | ~v1_partfun1('#skF_3', A_58) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(splitLeft, [status(thm)], [c_186])).
% 2.14/1.30  tff(c_191, plain, (~v1_partfun1('#skF_4', '#skF_1') | ~v1_partfun1('#skF_3', '#skF_1') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_134, c_188])).
% 2.14/1.30  tff(c_195, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_135, c_167, c_163, c_191])).
% 2.14/1.30  tff(c_196, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_186])).
% 2.14/1.30  tff(c_133, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_16])).
% 2.14/1.30  tff(c_200, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_196, c_133])).
% 2.14/1.30  tff(c_209, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_151, c_200])).
% 2.14/1.30  tff(c_210, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_143])).
% 2.14/1.30  tff(c_131, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_2])).
% 2.14/1.30  tff(c_215, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_210, c_131])).
% 2.14/1.30  tff(c_144, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_134, c_136])).
% 2.14/1.30  tff(c_251, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_210, c_215, c_144])).
% 2.14/1.30  tff(c_252, plain, (![A_63]: (A_63='#skF_4' | ~v1_xboole_0(A_63))), inference(demodulation, [status(thm), theory('equality')], [c_215, c_131])).
% 2.14/1.30  tff(c_259, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_251, c_252])).
% 2.14/1.30  tff(c_221, plain, (![A_60, B_61, D_62]: (r2_relset_1(A_60, B_61, D_62, D_62) | ~m1_subset_1(D_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.14/1.30  tff(c_227, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_134, c_221])).
% 2.14/1.30  tff(c_273, plain, (r2_relset_1('#skF_4', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_259, c_259, c_215, c_215, c_227])).
% 2.14/1.30  tff(c_231, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_215, c_215, c_133])).
% 2.14/1.30  tff(c_276, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_273, c_259, c_231])).
% 2.14/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.30  
% 2.14/1.30  Inference rules
% 2.14/1.30  ----------------------
% 2.14/1.30  #Ref     : 0
% 2.14/1.30  #Sup     : 39
% 2.14/1.30  #Fact    : 0
% 2.14/1.30  #Define  : 0
% 2.14/1.30  #Split   : 6
% 2.14/1.30  #Chain   : 0
% 2.14/1.30  #Close   : 0
% 2.14/1.30  
% 2.14/1.30  Ordering : KBO
% 2.14/1.30  
% 2.14/1.30  Simplification rules
% 2.14/1.30  ----------------------
% 2.14/1.30  #Subsume      : 2
% 2.14/1.30  #Demod        : 86
% 2.14/1.30  #Tautology    : 30
% 2.14/1.30  #SimpNegUnit  : 4
% 2.14/1.30  #BackRed      : 28
% 2.14/1.30  
% 2.14/1.30  #Partial instantiations: 0
% 2.14/1.30  #Strategies tried      : 1
% 2.14/1.30  
% 2.14/1.30  Timing (in seconds)
% 2.14/1.30  ----------------------
% 2.14/1.30  Preprocessing        : 0.32
% 2.14/1.30  Parsing              : 0.17
% 2.14/1.30  CNF conversion       : 0.02
% 2.14/1.30  Main loop            : 0.21
% 2.14/1.30  Inferencing          : 0.08
% 2.14/1.30  Reduction            : 0.07
% 2.14/1.30  Demodulation         : 0.05
% 2.14/1.30  BG Simplification    : 0.01
% 2.14/1.30  Subsumption          : 0.03
% 2.14/1.30  Abstraction          : 0.01
% 2.14/1.30  MUC search           : 0.00
% 2.14/1.30  Cooper               : 0.00
% 2.14/1.30  Total                : 0.57
% 2.14/1.30  Index Insertion      : 0.00
% 2.14/1.30  Index Deletion       : 0.00
% 2.14/1.30  Index Matching       : 0.00
% 2.14/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
