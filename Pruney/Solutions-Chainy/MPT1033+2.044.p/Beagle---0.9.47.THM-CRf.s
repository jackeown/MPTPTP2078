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
% DateTime   : Thu Dec  3 10:16:56 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 783 expanded)
%              Number of leaves         :   31 ( 247 expanded)
%              Depth                    :   11
%              Number of atoms          :  143 (2732 expanded)
%              Number of equality atoms :   49 (1072 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r2_hidden > r1_partfun1 > m1_subset_1 > v1_funct_1 > k3_partfun1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k3_partfun1,type,(
    k3_partfun1: ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_132,negated_conjecture,(
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

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k3_partfun1(C,A,B) = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_partfun1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => v1_partfun1(k3_partfun1(C,A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_funct_2)).

tff(f_83,axiom,(
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

tff(f_33,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(f_34,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_112,plain,(
    ! [A_41,B_42,D_43] :
      ( r2_relset_1(A_41,B_42,D_43,D_43)
      | ~ m1_subset_1(D_43,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_121,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_112])).

tff(c_34,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_83,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_48,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_46,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_125,plain,(
    ! [C_48,A_49,B_50] :
      ( k3_partfun1(C_48,A_49,B_50) = C_48
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50)))
      | ~ v1_funct_1(C_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_128,plain,
    ( k3_partfun1('#skF_4','#skF_2','#skF_3') = '#skF_4'
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_125])).

tff(c_140,plain,(
    k3_partfun1('#skF_4','#skF_2','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_128])).

tff(c_168,plain,(
    ! [B_61,C_62,A_63] :
      ( k1_xboole_0 = B_61
      | v1_partfun1(k3_partfun1(C_62,A_63,B_61),A_63)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_61)))
      | ~ v1_funct_2(C_62,A_63,B_61)
      | ~ v1_funct_1(C_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_170,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_partfun1(k3_partfun1('#skF_4','#skF_2','#skF_3'),'#skF_2')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_168])).

tff(c_179,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_partfun1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_140,c_170])).

tff(c_180,plain,(
    v1_partfun1('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_179])).

tff(c_42,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_40,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_131,plain,
    ( k3_partfun1('#skF_5','#skF_2','#skF_3') = '#skF_5'
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_125])).

tff(c_143,plain,(
    k3_partfun1('#skF_5','#skF_2','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_131])).

tff(c_172,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_partfun1(k3_partfun1('#skF_5','#skF_2','#skF_3'),'#skF_2')
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_168])).

tff(c_183,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_partfun1('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_143,c_172])).

tff(c_184,plain,(
    v1_partfun1('#skF_5','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_183])).

tff(c_36,plain,(
    r1_partfun1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_197,plain,(
    ! [D_68,C_69,A_70,B_71] :
      ( D_68 = C_69
      | ~ r1_partfun1(C_69,D_68)
      | ~ v1_partfun1(D_68,A_70)
      | ~ v1_partfun1(C_69,A_70)
      | ~ m1_subset_1(D_68,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71)))
      | ~ v1_funct_1(D_68)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71)))
      | ~ v1_funct_1(C_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_199,plain,(
    ! [A_70,B_71] :
      ( '#skF_5' = '#skF_4'
      | ~ v1_partfun1('#skF_5',A_70)
      | ~ v1_partfun1('#skF_4',A_70)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_70,B_71)))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_70,B_71)))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_36,c_197])).

tff(c_202,plain,(
    ! [A_70,B_71] :
      ( '#skF_5' = '#skF_4'
      | ~ v1_partfun1('#skF_5',A_70)
      | ~ v1_partfun1('#skF_4',A_70)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_70,B_71)))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_199])).

tff(c_221,plain,(
    ! [A_76,B_77] :
      ( ~ v1_partfun1('#skF_5',A_76)
      | ~ v1_partfun1('#skF_4',A_76)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_76,B_77)))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(splitLeft,[status(thm)],[c_202])).

tff(c_224,plain,
    ( ~ v1_partfun1('#skF_5','#skF_2')
    | ~ v1_partfun1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_38,c_221])).

tff(c_234,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_180,c_184,c_224])).

tff(c_235,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_202])).

tff(c_32,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_241,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_32])).

tff(c_252,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_241])).

tff(c_254,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_253,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_263,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_253])).

tff(c_8,plain,(
    ! [A_3] : k9_relat_1(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_255,plain,(
    ! [A_3] : k9_relat_1('#skF_2',A_3) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_253,c_8])).

tff(c_304,plain,(
    ! [A_3] : k9_relat_1('#skF_3',A_3) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_263,c_255])).

tff(c_10,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_258,plain,(
    k6_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_253,c_10])).

tff(c_275,plain,(
    k6_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_263,c_258])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_256,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_253,c_4])).

tff(c_280,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_263,c_256])).

tff(c_313,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_263,c_44])).

tff(c_326,plain,(
    ! [A_83,B_84] :
      ( k9_relat_1(k6_relat_1(A_83),B_84) = B_84
      | ~ m1_subset_1(B_84,k1_zfmisc_1(A_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_329,plain,(
    k9_relat_1(k6_relat_1('#skF_3'),'#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_313,c_326])).

tff(c_334,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_275,c_329])).

tff(c_338,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_334,c_313])).

tff(c_375,plain,(
    ! [A_88] : k2_zfmisc_1(A_88,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_334,c_334,c_280])).

tff(c_14,plain,(
    ! [A_6,B_7,D_9] :
      ( r2_relset_1(A_6,B_7,D_9,D_9)
      | ~ m1_subset_1(D_9,k1_zfmisc_1(k2_zfmisc_1(A_6,B_7))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_434,plain,(
    ! [A_96,D_97] :
      ( r2_relset_1(A_96,'#skF_4',D_97,D_97)
      | ~ m1_subset_1(D_97,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_375,c_14])).

tff(c_437,plain,(
    ! [A_96] : r2_relset_1(A_96,'#skF_4','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_338,c_434])).

tff(c_312,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_263,c_38])).

tff(c_332,plain,(
    k9_relat_1(k6_relat_1('#skF_3'),'#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_312,c_326])).

tff(c_336,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_275,c_332])).

tff(c_354,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_334,c_336])).

tff(c_268,plain,(
    ~ r2_relset_1('#skF_3','#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_32])).

tff(c_339,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_334,c_334,c_268])).

tff(c_422,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_354,c_339])).

tff(c_440,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_437,c_422])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n024.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 15:31:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.37/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.36  
% 2.37/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.36  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r2_hidden > r1_partfun1 > m1_subset_1 > v1_funct_1 > k3_partfun1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.37/1.36  
% 2.37/1.36  %Foreground sorts:
% 2.37/1.36  
% 2.37/1.36  
% 2.37/1.36  %Background operators:
% 2.37/1.36  
% 2.37/1.36  
% 2.37/1.36  %Foreground operators:
% 2.37/1.36  tff(k3_partfun1, type, k3_partfun1: ($i * $i * $i) > $i).
% 2.37/1.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.37/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.37/1.36  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.37/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.37/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.37/1.36  tff('#skF_5', type, '#skF_5': $i).
% 2.37/1.36  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.37/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.37/1.36  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.37/1.36  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.37/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.37/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.37/1.36  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.37/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.37/1.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.37/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.37/1.36  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.37/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.37/1.36  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.37/1.36  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 2.37/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.37/1.36  
% 2.65/1.38  tff(f_132, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_relset_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_2)).
% 2.65/1.38  tff(f_46, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.65/1.38  tff(f_109, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k3_partfun1(C, A, B) = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_partfun1)).
% 2.65/1.38  tff(f_66, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => v1_partfun1(k3_partfun1(C, A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t133_funct_2)).
% 2.65/1.38  tff(f_83, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_partfun1)).
% 2.65/1.38  tff(f_33, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 2.65/1.38  tff(f_34, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 2.65/1.38  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.65/1.38  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_funct_1)).
% 2.65/1.38  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.65/1.38  tff(c_112, plain, (![A_41, B_42, D_43]: (r2_relset_1(A_41, B_42, D_43, D_43) | ~m1_subset_1(D_43, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.65/1.38  tff(c_121, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_112])).
% 2.65/1.38  tff(c_34, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.65/1.38  tff(c_83, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_34])).
% 2.65/1.38  tff(c_48, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.65/1.38  tff(c_46, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.65/1.38  tff(c_125, plain, (![C_48, A_49, B_50]: (k3_partfun1(C_48, A_49, B_50)=C_48 | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))) | ~v1_funct_1(C_48))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.65/1.38  tff(c_128, plain, (k3_partfun1('#skF_4', '#skF_2', '#skF_3')='#skF_4' | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_125])).
% 2.65/1.38  tff(c_140, plain, (k3_partfun1('#skF_4', '#skF_2', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_128])).
% 2.65/1.38  tff(c_168, plain, (![B_61, C_62, A_63]: (k1_xboole_0=B_61 | v1_partfun1(k3_partfun1(C_62, A_63, B_61), A_63) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_61))) | ~v1_funct_2(C_62, A_63, B_61) | ~v1_funct_1(C_62))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.65/1.38  tff(c_170, plain, (k1_xboole_0='#skF_3' | v1_partfun1(k3_partfun1('#skF_4', '#skF_2', '#skF_3'), '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_168])).
% 2.65/1.38  tff(c_179, plain, (k1_xboole_0='#skF_3' | v1_partfun1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_140, c_170])).
% 2.65/1.38  tff(c_180, plain, (v1_partfun1('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_83, c_179])).
% 2.65/1.38  tff(c_42, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.65/1.38  tff(c_40, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.65/1.38  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.65/1.38  tff(c_131, plain, (k3_partfun1('#skF_5', '#skF_2', '#skF_3')='#skF_5' | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_125])).
% 2.65/1.38  tff(c_143, plain, (k3_partfun1('#skF_5', '#skF_2', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_131])).
% 2.65/1.38  tff(c_172, plain, (k1_xboole_0='#skF_3' | v1_partfun1(k3_partfun1('#skF_5', '#skF_2', '#skF_3'), '#skF_2') | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_168])).
% 2.65/1.38  tff(c_183, plain, (k1_xboole_0='#skF_3' | v1_partfun1('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_143, c_172])).
% 2.65/1.38  tff(c_184, plain, (v1_partfun1('#skF_5', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_83, c_183])).
% 2.65/1.38  tff(c_36, plain, (r1_partfun1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.65/1.38  tff(c_197, plain, (![D_68, C_69, A_70, B_71]: (D_68=C_69 | ~r1_partfun1(C_69, D_68) | ~v1_partfun1(D_68, A_70) | ~v1_partfun1(C_69, A_70) | ~m1_subset_1(D_68, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))) | ~v1_funct_1(D_68) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))) | ~v1_funct_1(C_69))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.65/1.38  tff(c_199, plain, (![A_70, B_71]: ('#skF_5'='#skF_4' | ~v1_partfun1('#skF_5', A_70) | ~v1_partfun1('#skF_4', A_70) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_36, c_197])).
% 2.65/1.38  tff(c_202, plain, (![A_70, B_71]: ('#skF_5'='#skF_4' | ~v1_partfun1('#skF_5', A_70) | ~v1_partfun1('#skF_4', A_70) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_42, c_199])).
% 2.65/1.38  tff(c_221, plain, (![A_76, B_77]: (~v1_partfun1('#skF_5', A_76) | ~v1_partfun1('#skF_4', A_76) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(splitLeft, [status(thm)], [c_202])).
% 2.65/1.38  tff(c_224, plain, (~v1_partfun1('#skF_5', '#skF_2') | ~v1_partfun1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_38, c_221])).
% 2.65/1.38  tff(c_234, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_180, c_184, c_224])).
% 2.65/1.38  tff(c_235, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_202])).
% 2.65/1.38  tff(c_32, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.65/1.38  tff(c_241, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_235, c_32])).
% 2.65/1.38  tff(c_252, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_121, c_241])).
% 2.65/1.38  tff(c_254, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_34])).
% 2.65/1.38  tff(c_253, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_34])).
% 2.65/1.38  tff(c_263, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_254, c_253])).
% 2.65/1.38  tff(c_8, plain, (![A_3]: (k9_relat_1(k1_xboole_0, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.65/1.38  tff(c_255, plain, (![A_3]: (k9_relat_1('#skF_2', A_3)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_253, c_253, c_8])).
% 2.65/1.38  tff(c_304, plain, (![A_3]: (k9_relat_1('#skF_3', A_3)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_263, c_263, c_255])).
% 2.65/1.38  tff(c_10, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.65/1.38  tff(c_258, plain, (k6_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_253, c_253, c_10])).
% 2.65/1.38  tff(c_275, plain, (k6_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_263, c_263, c_258])).
% 2.65/1.38  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.65/1.38  tff(c_256, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_253, c_253, c_4])).
% 2.65/1.38  tff(c_280, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_263, c_263, c_256])).
% 2.65/1.38  tff(c_313, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_280, c_263, c_44])).
% 2.65/1.38  tff(c_326, plain, (![A_83, B_84]: (k9_relat_1(k6_relat_1(A_83), B_84)=B_84 | ~m1_subset_1(B_84, k1_zfmisc_1(A_83)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.65/1.38  tff(c_329, plain, (k9_relat_1(k6_relat_1('#skF_3'), '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_313, c_326])).
% 2.65/1.38  tff(c_334, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_304, c_275, c_329])).
% 2.65/1.38  tff(c_338, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_334, c_313])).
% 2.65/1.38  tff(c_375, plain, (![A_88]: (k2_zfmisc_1(A_88, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_334, c_334, c_280])).
% 2.65/1.38  tff(c_14, plain, (![A_6, B_7, D_9]: (r2_relset_1(A_6, B_7, D_9, D_9) | ~m1_subset_1(D_9, k1_zfmisc_1(k2_zfmisc_1(A_6, B_7))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.65/1.38  tff(c_434, plain, (![A_96, D_97]: (r2_relset_1(A_96, '#skF_4', D_97, D_97) | ~m1_subset_1(D_97, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_375, c_14])).
% 2.65/1.38  tff(c_437, plain, (![A_96]: (r2_relset_1(A_96, '#skF_4', '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_338, c_434])).
% 2.65/1.38  tff(c_312, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_280, c_263, c_38])).
% 2.65/1.38  tff(c_332, plain, (k9_relat_1(k6_relat_1('#skF_3'), '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_312, c_326])).
% 2.65/1.38  tff(c_336, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_304, c_275, c_332])).
% 2.65/1.38  tff(c_354, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_334, c_336])).
% 2.65/1.38  tff(c_268, plain, (~r2_relset_1('#skF_3', '#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_263, c_32])).
% 2.65/1.38  tff(c_339, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_334, c_334, c_268])).
% 2.65/1.38  tff(c_422, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_354, c_339])).
% 2.65/1.38  tff(c_440, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_437, c_422])).
% 2.65/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.38  
% 2.65/1.38  Inference rules
% 2.65/1.38  ----------------------
% 2.65/1.38  #Ref     : 0
% 2.65/1.38  #Sup     : 92
% 2.65/1.38  #Fact    : 0
% 2.65/1.38  #Define  : 0
% 2.65/1.38  #Split   : 2
% 2.65/1.38  #Chain   : 0
% 2.65/1.38  #Close   : 0
% 2.65/1.38  
% 2.65/1.38  Ordering : KBO
% 2.65/1.38  
% 2.65/1.38  Simplification rules
% 2.65/1.38  ----------------------
% 2.65/1.38  #Subsume      : 1
% 2.65/1.38  #Demod        : 108
% 2.65/1.38  #Tautology    : 72
% 2.65/1.38  #SimpNegUnit  : 2
% 2.65/1.38  #BackRed      : 32
% 2.65/1.38  
% 2.65/1.38  #Partial instantiations: 0
% 2.65/1.38  #Strategies tried      : 1
% 2.65/1.38  
% 2.65/1.38  Timing (in seconds)
% 2.65/1.38  ----------------------
% 2.65/1.38  Preprocessing        : 0.34
% 2.65/1.38  Parsing              : 0.19
% 2.65/1.38  CNF conversion       : 0.02
% 2.65/1.38  Main loop            : 0.25
% 2.65/1.38  Inferencing          : 0.08
% 2.65/1.38  Reduction            : 0.09
% 2.65/1.38  Demodulation         : 0.06
% 2.65/1.38  BG Simplification    : 0.02
% 2.65/1.38  Subsumption          : 0.04
% 2.65/1.38  Abstraction          : 0.01
% 2.65/1.38  MUC search           : 0.00
% 2.65/1.38  Cooper               : 0.00
% 2.65/1.38  Total                : 0.63
% 2.65/1.38  Index Insertion      : 0.00
% 2.65/1.38  Index Deletion       : 0.00
% 2.65/1.38  Index Matching       : 0.00
% 2.65/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
