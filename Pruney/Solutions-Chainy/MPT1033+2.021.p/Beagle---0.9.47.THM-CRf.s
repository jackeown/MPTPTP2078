%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:53 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 588 expanded)
%              Number of leaves         :   23 ( 186 expanded)
%              Depth                    :   11
%              Number of atoms          :  191 (2077 expanded)
%              Number of equality atoms :   25 ( 552 expanded)
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

tff(f_36,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

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

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_18,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_33,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_18])).

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

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_35,plain,(
    ! [C_21,B_22,A_23] :
      ( v1_xboole_0(C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(B_22,A_23)))
      | ~ v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_42,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_35])).

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_32,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_30,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
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

tff(c_62,plain,(
    v1_partfun1('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_61])).

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

tff(c_65,plain,
    ( v1_partfun1('#skF_4','#skF_1')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_58])).

tff(c_66,plain,(
    v1_partfun1('#skF_4','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_65])).

tff(c_20,plain,(
    r1_partfun1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_80,plain,(
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

tff(c_82,plain,(
    ! [A_36,B_37] :
      ( '#skF_3' = '#skF_4'
      | ~ v1_partfun1('#skF_4',A_36)
      | ~ v1_partfun1('#skF_3',A_36)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_36,B_37)))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_36,B_37)))
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_80])).

tff(c_85,plain,(
    ! [A_36,B_37] :
      ( '#skF_3' = '#skF_4'
      | ~ v1_partfun1('#skF_4',A_36)
      | ~ v1_partfun1('#skF_3',A_36)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_36,B_37)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_26,c_82])).

tff(c_87,plain,(
    ! [A_38,B_39] :
      ( ~ v1_partfun1('#skF_4',A_38)
      | ~ v1_partfun1('#skF_3',A_38)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_38,B_39)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(splitLeft,[status(thm)],[c_85])).

tff(c_90,plain,
    ( ~ v1_partfun1('#skF_4','#skF_1')
    | ~ v1_partfun1('#skF_3','#skF_1')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_28,c_87])).

tff(c_94,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_62,c_66,c_90])).

tff(c_95,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_16,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_99,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_16])).

tff(c_108,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_99])).

tff(c_110,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_117,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_110,c_2])).

tff(c_121,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33,c_117])).

tff(c_122,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_123,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_128,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_123])).

tff(c_138,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_22])).

tff(c_151,plain,(
    ! [A_44,B_45,D_46] :
      ( r2_relset_1(A_44,B_45,D_46,D_46)
      | ~ m1_subset_1(D_46,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_157,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_138,c_151])).

tff(c_139,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_28])).

tff(c_140,plain,(
    ! [C_41,B_42,A_43] :
      ( v1_xboole_0(C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(B_42,A_43)))
      | ~ v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_147,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_139,c_140])).

tff(c_149,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_147])).

tff(c_130,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_30])).

tff(c_158,plain,(
    ! [C_47,A_48,B_49] :
      ( v1_partfun1(C_47,A_48)
      | ~ v1_funct_2(C_47,A_48,B_49)
      | ~ v1_funct_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49)))
      | v1_xboole_0(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_161,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_139,c_158])).

tff(c_167,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_130,c_161])).

tff(c_168,plain,(
    v1_partfun1('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_167])).

tff(c_129,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_24])).

tff(c_164,plain,
    ( v1_partfun1('#skF_4','#skF_1')
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_138,c_158])).

tff(c_171,plain,
    ( v1_partfun1('#skF_4','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_129,c_164])).

tff(c_172,plain,(
    v1_partfun1('#skF_4','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_171])).

tff(c_186,plain,(
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

tff(c_188,plain,(
    ! [A_56,B_57] :
      ( '#skF_3' = '#skF_4'
      | ~ v1_partfun1('#skF_4',A_56)
      | ~ v1_partfun1('#skF_3',A_56)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_56,B_57)))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_56,B_57)))
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_186])).

tff(c_191,plain,(
    ! [A_56,B_57] :
      ( '#skF_3' = '#skF_4'
      | ~ v1_partfun1('#skF_4',A_56)
      | ~ v1_partfun1('#skF_3',A_56)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_56,B_57)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_26,c_188])).

tff(c_193,plain,(
    ! [A_58,B_59] :
      ( ~ v1_partfun1('#skF_4',A_58)
      | ~ v1_partfun1('#skF_3',A_58)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_58,B_59)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(splitLeft,[status(thm)],[c_191])).

tff(c_196,plain,
    ( ~ v1_partfun1('#skF_4','#skF_1')
    | ~ v1_partfun1('#skF_3','#skF_1')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_139,c_193])).

tff(c_200,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_168,c_172,c_196])).

tff(c_201,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_191])).

tff(c_137,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_16])).

tff(c_205,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_137])).

tff(c_214,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_205])).

tff(c_216,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_147])).

tff(c_148,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_138,c_140])).

tff(c_245,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_148])).

tff(c_135,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_2])).

tff(c_249,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_245,c_135])).

tff(c_215,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_147])).

tff(c_220,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_215,c_135])).

tff(c_252,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_220])).

tff(c_226,plain,(
    ! [A_60,B_61,D_62] :
      ( r2_relset_1(A_60,B_61,D_62,D_62)
      | ~ m1_subset_1(D_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_231,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_139,c_226])).

tff(c_286,plain,(
    r2_relset_1('#skF_4','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_252,c_249,c_249,c_231])).

tff(c_235,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_137])).

tff(c_289,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_249,c_249,c_249,c_235])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:07:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.29  
% 2.10/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.29  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.10/1.29  
% 2.10/1.29  %Foreground sorts:
% 2.10/1.29  
% 2.10/1.29  
% 2.10/1.29  %Background operators:
% 2.10/1.29  
% 2.10/1.29  
% 2.10/1.29  %Foreground operators:
% 2.10/1.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.10/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.29  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.10/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.10/1.29  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.10/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.10/1.29  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.10/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.10/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.10/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.10/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.10/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.10/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.10/1.29  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 2.10/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.10/1.29  
% 2.36/1.31  tff(f_98, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_relset_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_2)).
% 2.36/1.31  tff(f_44, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.36/1.31  tff(f_36, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 2.36/1.31  tff(f_58, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.36/1.31  tff(f_75, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_partfun1)).
% 2.36/1.31  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.36/1.31  tff(c_18, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.36/1.31  tff(c_33, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_18])).
% 2.36/1.31  tff(c_22, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.36/1.31  tff(c_45, plain, (![A_24, B_25, D_26]: (r2_relset_1(A_24, B_25, D_26, D_26) | ~m1_subset_1(D_26, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.36/1.31  tff(c_51, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_22, c_45])).
% 2.36/1.31  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.36/1.31  tff(c_35, plain, (![C_21, B_22, A_23]: (v1_xboole_0(C_21) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(B_22, A_23))) | ~v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.36/1.31  tff(c_42, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_28, c_35])).
% 2.36/1.31  tff(c_44, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_42])).
% 2.36/1.31  tff(c_32, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.36/1.31  tff(c_30, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.36/1.31  tff(c_52, plain, (![C_27, A_28, B_29]: (v1_partfun1(C_27, A_28) | ~v1_funct_2(C_27, A_28, B_29) | ~v1_funct_1(C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))) | v1_xboole_0(B_29))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.36/1.31  tff(c_55, plain, (v1_partfun1('#skF_3', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_28, c_52])).
% 2.36/1.31  tff(c_61, plain, (v1_partfun1('#skF_3', '#skF_1') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_55])).
% 2.36/1.31  tff(c_62, plain, (v1_partfun1('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_44, c_61])).
% 2.36/1.31  tff(c_26, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.36/1.31  tff(c_24, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.36/1.31  tff(c_58, plain, (v1_partfun1('#skF_4', '#skF_1') | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_22, c_52])).
% 2.36/1.31  tff(c_65, plain, (v1_partfun1('#skF_4', '#skF_1') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_58])).
% 2.36/1.31  tff(c_66, plain, (v1_partfun1('#skF_4', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_44, c_65])).
% 2.36/1.31  tff(c_20, plain, (r1_partfun1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.36/1.31  tff(c_80, plain, (![D_34, C_35, A_36, B_37]: (D_34=C_35 | ~r1_partfun1(C_35, D_34) | ~v1_partfun1(D_34, A_36) | ~v1_partfun1(C_35, A_36) | ~m1_subset_1(D_34, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))) | ~v1_funct_1(D_34) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))) | ~v1_funct_1(C_35))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.36/1.31  tff(c_82, plain, (![A_36, B_37]: ('#skF_3'='#skF_4' | ~v1_partfun1('#skF_4', A_36) | ~v1_partfun1('#skF_3', A_36) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_20, c_80])).
% 2.36/1.31  tff(c_85, plain, (![A_36, B_37]: ('#skF_3'='#skF_4' | ~v1_partfun1('#skF_4', A_36) | ~v1_partfun1('#skF_3', A_36) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_26, c_82])).
% 2.36/1.31  tff(c_87, plain, (![A_38, B_39]: (~v1_partfun1('#skF_4', A_38) | ~v1_partfun1('#skF_3', A_38) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(splitLeft, [status(thm)], [c_85])).
% 2.36/1.31  tff(c_90, plain, (~v1_partfun1('#skF_4', '#skF_1') | ~v1_partfun1('#skF_3', '#skF_1') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_28, c_87])).
% 2.36/1.31  tff(c_94, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_62, c_66, c_90])).
% 2.36/1.31  tff(c_95, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_85])).
% 2.36/1.31  tff(c_16, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.36/1.31  tff(c_99, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_16])).
% 2.36/1.31  tff(c_108, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_51, c_99])).
% 2.36/1.31  tff(c_110, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_42])).
% 2.36/1.31  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.36/1.31  tff(c_117, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_110, c_2])).
% 2.36/1.31  tff(c_121, plain, $false, inference(negUnitSimplification, [status(thm)], [c_33, c_117])).
% 2.36/1.31  tff(c_122, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_18])).
% 2.36/1.31  tff(c_123, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_18])).
% 2.36/1.31  tff(c_128, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_122, c_123])).
% 2.36/1.31  tff(c_138, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_22])).
% 2.36/1.31  tff(c_151, plain, (![A_44, B_45, D_46]: (r2_relset_1(A_44, B_45, D_46, D_46) | ~m1_subset_1(D_46, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.36/1.31  tff(c_157, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_138, c_151])).
% 2.36/1.31  tff(c_139, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_28])).
% 2.36/1.31  tff(c_140, plain, (![C_41, B_42, A_43]: (v1_xboole_0(C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(B_42, A_43))) | ~v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.36/1.31  tff(c_147, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_139, c_140])).
% 2.36/1.31  tff(c_149, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_147])).
% 2.36/1.31  tff(c_130, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_30])).
% 2.36/1.31  tff(c_158, plain, (![C_47, A_48, B_49]: (v1_partfun1(C_47, A_48) | ~v1_funct_2(C_47, A_48, B_49) | ~v1_funct_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))) | v1_xboole_0(B_49))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.36/1.31  tff(c_161, plain, (v1_partfun1('#skF_3', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_139, c_158])).
% 2.36/1.31  tff(c_167, plain, (v1_partfun1('#skF_3', '#skF_1') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_130, c_161])).
% 2.36/1.31  tff(c_168, plain, (v1_partfun1('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_149, c_167])).
% 2.36/1.31  tff(c_129, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_24])).
% 2.36/1.31  tff(c_164, plain, (v1_partfun1('#skF_4', '#skF_1') | ~v1_funct_2('#skF_4', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_138, c_158])).
% 2.36/1.31  tff(c_171, plain, (v1_partfun1('#skF_4', '#skF_1') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_129, c_164])).
% 2.36/1.31  tff(c_172, plain, (v1_partfun1('#skF_4', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_149, c_171])).
% 2.36/1.31  tff(c_186, plain, (![D_54, C_55, A_56, B_57]: (D_54=C_55 | ~r1_partfun1(C_55, D_54) | ~v1_partfun1(D_54, A_56) | ~v1_partfun1(C_55, A_56) | ~m1_subset_1(D_54, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))) | ~v1_funct_1(D_54) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))) | ~v1_funct_1(C_55))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.36/1.31  tff(c_188, plain, (![A_56, B_57]: ('#skF_3'='#skF_4' | ~v1_partfun1('#skF_4', A_56) | ~v1_partfun1('#skF_3', A_56) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_20, c_186])).
% 2.36/1.31  tff(c_191, plain, (![A_56, B_57]: ('#skF_3'='#skF_4' | ~v1_partfun1('#skF_4', A_56) | ~v1_partfun1('#skF_3', A_56) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_26, c_188])).
% 2.36/1.31  tff(c_193, plain, (![A_58, B_59]: (~v1_partfun1('#skF_4', A_58) | ~v1_partfun1('#skF_3', A_58) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(splitLeft, [status(thm)], [c_191])).
% 2.36/1.31  tff(c_196, plain, (~v1_partfun1('#skF_4', '#skF_1') | ~v1_partfun1('#skF_3', '#skF_1') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_139, c_193])).
% 2.36/1.31  tff(c_200, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_138, c_168, c_172, c_196])).
% 2.36/1.31  tff(c_201, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_191])).
% 2.36/1.31  tff(c_137, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_16])).
% 2.36/1.31  tff(c_205, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_201, c_137])).
% 2.36/1.31  tff(c_214, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_157, c_205])).
% 2.36/1.31  tff(c_216, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_147])).
% 2.36/1.31  tff(c_148, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_138, c_140])).
% 2.36/1.31  tff(c_245, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_216, c_148])).
% 2.36/1.31  tff(c_135, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_2])).
% 2.36/1.31  tff(c_249, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_245, c_135])).
% 2.36/1.31  tff(c_215, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_147])).
% 2.36/1.31  tff(c_220, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_215, c_135])).
% 2.36/1.31  tff(c_252, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_249, c_220])).
% 2.36/1.31  tff(c_226, plain, (![A_60, B_61, D_62]: (r2_relset_1(A_60, B_61, D_62, D_62) | ~m1_subset_1(D_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.36/1.31  tff(c_231, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_139, c_226])).
% 2.36/1.31  tff(c_286, plain, (r2_relset_1('#skF_4', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_252, c_252, c_249, c_249, c_231])).
% 2.36/1.31  tff(c_235, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_220, c_137])).
% 2.36/1.31  tff(c_289, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_286, c_249, c_249, c_249, c_235])).
% 2.36/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.31  
% 2.36/1.31  Inference rules
% 2.36/1.31  ----------------------
% 2.36/1.31  #Ref     : 0
% 2.36/1.31  #Sup     : 42
% 2.36/1.31  #Fact    : 0
% 2.36/1.31  #Define  : 0
% 2.36/1.31  #Split   : 6
% 2.36/1.31  #Chain   : 0
% 2.36/1.31  #Close   : 0
% 2.36/1.31  
% 2.36/1.31  Ordering : KBO
% 2.36/1.31  
% 2.36/1.31  Simplification rules
% 2.36/1.31  ----------------------
% 2.36/1.31  #Subsume      : 2
% 2.36/1.31  #Demod        : 89
% 2.36/1.31  #Tautology    : 32
% 2.36/1.31  #SimpNegUnit  : 5
% 2.36/1.31  #BackRed      : 31
% 2.36/1.31  
% 2.36/1.31  #Partial instantiations: 0
% 2.36/1.31  #Strategies tried      : 1
% 2.36/1.31  
% 2.36/1.31  Timing (in seconds)
% 2.36/1.31  ----------------------
% 2.36/1.32  Preprocessing        : 0.31
% 2.36/1.32  Parsing              : 0.17
% 2.36/1.32  CNF conversion       : 0.02
% 2.36/1.32  Main loop            : 0.22
% 2.36/1.32  Inferencing          : 0.08
% 2.36/1.32  Reduction            : 0.07
% 2.36/1.32  Demodulation         : 0.05
% 2.36/1.32  BG Simplification    : 0.01
% 2.36/1.32  Subsumption          : 0.03
% 2.36/1.32  Abstraction          : 0.01
% 2.36/1.32  MUC search           : 0.00
% 2.36/1.32  Cooper               : 0.00
% 2.36/1.32  Total                : 0.57
% 2.36/1.32  Index Insertion      : 0.00
% 2.36/1.32  Index Deletion       : 0.00
% 2.36/1.32  Index Matching       : 0.00
% 2.36/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
