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
% DateTime   : Thu Dec  3 10:16:51 EST 2020

% Result     : Theorem 2.85s
% Output     : CNFRefutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 523 expanded)
%              Number of leaves         :   27 ( 196 expanded)
%              Depth                    :   12
%              Number of atoms          :  144 (1191 expanded)
%              Number of equality atoms :   30 ( 373 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_31,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_116,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_2)).

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_93,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(c_4,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_53,plain,(
    ! [A_26] :
      ( k1_xboole_0 = A_26
      | ~ v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_57,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_53])).

tff(c_16,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_63,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_57,c_16])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_163,plain,(
    ! [A_42,B_43,D_44] :
      ( r2_relset_1(A_42,B_43,D_44,D_44)
      | ~ m1_subset_1(D_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_176,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_163])).

tff(c_36,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_71,plain,
    ( '#skF_2' = '#skF_1'
    | '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_57,c_36])).

tff(c_72,plain,(
    '#skF_3' != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_71])).

tff(c_50,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_48,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_178,plain,(
    ! [C_45,A_46,B_47] :
      ( v1_partfun1(C_45,A_46)
      | ~ v1_funct_2(C_45,A_46,B_47)
      | ~ v1_funct_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47)))
      | v1_xboole_0(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_185,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_178])).

tff(c_198,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_185])).

tff(c_203,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_198])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_58,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_2])).

tff(c_206,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_203,c_58])).

tff(c_210,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_206])).

tff(c_211,plain,(
    v1_partfun1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_198])).

tff(c_212,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_198])).

tff(c_44,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_42,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_188,plain,
    ( v1_partfun1('#skF_5','#skF_2')
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_178])).

tff(c_201,plain,
    ( v1_partfun1('#skF_5','#skF_2')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_188])).

tff(c_213,plain,(
    v1_partfun1('#skF_5','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_212,c_201])).

tff(c_38,plain,(
    r1_partfun1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_293,plain,(
    ! [D_66,C_67,A_68,B_69] :
      ( D_66 = C_67
      | ~ r1_partfun1(C_67,D_66)
      | ~ v1_partfun1(D_66,A_68)
      | ~ v1_partfun1(C_67,A_68)
      | ~ m1_subset_1(D_66,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69)))
      | ~ v1_funct_1(D_66)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69)))
      | ~ v1_funct_1(C_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_295,plain,(
    ! [A_68,B_69] :
      ( '#skF_5' = '#skF_4'
      | ~ v1_partfun1('#skF_5',A_68)
      | ~ v1_partfun1('#skF_4',A_68)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_68,B_69)))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_68,B_69)))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_38,c_293])).

tff(c_298,plain,(
    ! [A_68,B_69] :
      ( '#skF_5' = '#skF_4'
      | ~ v1_partfun1('#skF_5',A_68)
      | ~ v1_partfun1('#skF_4',A_68)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_68,B_69)))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_44,c_295])).

tff(c_347,plain,(
    ! [A_80,B_81] :
      ( ~ v1_partfun1('#skF_5',A_80)
      | ~ v1_partfun1('#skF_4',A_80)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_80,B_81)))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(splitLeft,[status(thm)],[c_298])).

tff(c_353,plain,
    ( ~ v1_partfun1('#skF_5','#skF_2')
    | ~ v1_partfun1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_40,c_347])).

tff(c_364,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_211,c_213,c_353])).

tff(c_365,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_298])).

tff(c_34,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_371,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_365,c_34])).

tff(c_381,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_371])).

tff(c_382,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_419,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_382,c_46])).

tff(c_434,plain,(
    ! [B_88,A_89] :
      ( v1_xboole_0(B_88)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(A_89))
      | ~ v1_xboole_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_440,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_419,c_434])).

tff(c_447,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_440])).

tff(c_467,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_447,c_58])).

tff(c_474,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_467,c_419])).

tff(c_483,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_4',B_5) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_467,c_467,c_63])).

tff(c_571,plain,(
    ! [A_97,B_98,D_99] :
      ( r2_relset_1(A_97,B_98,D_99,D_99)
      | ~ m1_subset_1(D_99,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_601,plain,(
    ! [B_105,D_106] :
      ( r2_relset_1('#skF_4',B_105,D_106,D_106)
      | ~ m1_subset_1(D_106,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_483,c_571])).

tff(c_607,plain,(
    ! [B_105] : r2_relset_1('#skF_4',B_105,'#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_474,c_601])).

tff(c_418,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_382,c_40])).

tff(c_443,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_418,c_434])).

tff(c_450,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_443])).

tff(c_471,plain,(
    '#skF_5' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_450,c_58])).

tff(c_504,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_467,c_471])).

tff(c_383,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_410,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_383,c_382,c_34])).

tff(c_478,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_467,c_467,c_410])).

tff(c_582,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_504,c_478])).

tff(c_611,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_607,c_582])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:55:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.85/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.85/1.48  
% 2.85/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.85/1.48  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.85/1.48  
% 2.85/1.48  %Foreground sorts:
% 2.85/1.48  
% 2.85/1.48  
% 2.85/1.48  %Background operators:
% 2.85/1.48  
% 2.85/1.48  
% 2.85/1.48  %Foreground operators:
% 2.85/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.85/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.85/1.48  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.85/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.85/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.85/1.48  tff('#skF_5', type, '#skF_5': $i).
% 2.85/1.48  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.85/1.48  tff('#skF_2', type, '#skF_2': $i).
% 2.85/1.48  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.85/1.48  tff('#skF_3', type, '#skF_3': $i).
% 2.85/1.48  tff('#skF_1', type, '#skF_1': $i).
% 2.85/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.85/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.85/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.85/1.48  tff('#skF_4', type, '#skF_4': $i).
% 2.85/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.85/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.85/1.48  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 2.85/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.85/1.48  
% 2.99/1.50  tff(f_31, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_xboole_0)).
% 2.99/1.50  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.99/1.50  tff(f_43, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.99/1.50  tff(f_116, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_relset_1(A, B, C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_2)).
% 2.99/1.50  tff(f_62, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.99/1.50  tff(f_76, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.99/1.50  tff(f_93, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_partfun1)).
% 2.99/1.50  tff(f_50, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.99/1.50  tff(c_4, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.99/1.50  tff(c_53, plain, (![A_26]: (k1_xboole_0=A_26 | ~v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.99/1.50  tff(c_57, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_4, c_53])).
% 2.99/1.50  tff(c_16, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.99/1.50  tff(c_63, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_57, c_57, c_16])).
% 2.99/1.50  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.99/1.50  tff(c_163, plain, (![A_42, B_43, D_44]: (r2_relset_1(A_42, B_43, D_44, D_44) | ~m1_subset_1(D_44, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.99/1.50  tff(c_176, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_163])).
% 2.99/1.50  tff(c_36, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.99/1.50  tff(c_71, plain, ('#skF_2'='#skF_1' | '#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_57, c_57, c_36])).
% 2.99/1.50  tff(c_72, plain, ('#skF_3'!='#skF_1'), inference(splitLeft, [status(thm)], [c_71])).
% 2.99/1.50  tff(c_50, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.99/1.50  tff(c_48, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.99/1.50  tff(c_178, plain, (![C_45, A_46, B_47]: (v1_partfun1(C_45, A_46) | ~v1_funct_2(C_45, A_46, B_47) | ~v1_funct_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))) | v1_xboole_0(B_47))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.99/1.50  tff(c_185, plain, (v1_partfun1('#skF_4', '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_46, c_178])).
% 2.99/1.50  tff(c_198, plain, (v1_partfun1('#skF_4', '#skF_2') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_185])).
% 2.99/1.50  tff(c_203, plain, (v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_198])).
% 2.99/1.50  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.99/1.50  tff(c_58, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_2])).
% 2.99/1.50  tff(c_206, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_203, c_58])).
% 2.99/1.50  tff(c_210, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_206])).
% 2.99/1.50  tff(c_211, plain, (v1_partfun1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_198])).
% 2.99/1.50  tff(c_212, plain, (~v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_198])).
% 2.99/1.50  tff(c_44, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.99/1.50  tff(c_42, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.99/1.50  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.99/1.50  tff(c_188, plain, (v1_partfun1('#skF_5', '#skF_2') | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_40, c_178])).
% 2.99/1.50  tff(c_201, plain, (v1_partfun1('#skF_5', '#skF_2') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_188])).
% 2.99/1.50  tff(c_213, plain, (v1_partfun1('#skF_5', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_212, c_201])).
% 2.99/1.50  tff(c_38, plain, (r1_partfun1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.99/1.50  tff(c_293, plain, (![D_66, C_67, A_68, B_69]: (D_66=C_67 | ~r1_partfun1(C_67, D_66) | ~v1_partfun1(D_66, A_68) | ~v1_partfun1(C_67, A_68) | ~m1_subset_1(D_66, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))) | ~v1_funct_1(D_66) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))) | ~v1_funct_1(C_67))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.99/1.50  tff(c_295, plain, (![A_68, B_69]: ('#skF_5'='#skF_4' | ~v1_partfun1('#skF_5', A_68) | ~v1_partfun1('#skF_4', A_68) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_38, c_293])).
% 2.99/1.50  tff(c_298, plain, (![A_68, B_69]: ('#skF_5'='#skF_4' | ~v1_partfun1('#skF_5', A_68) | ~v1_partfun1('#skF_4', A_68) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_44, c_295])).
% 2.99/1.50  tff(c_347, plain, (![A_80, B_81]: (~v1_partfun1('#skF_5', A_80) | ~v1_partfun1('#skF_4', A_80) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(splitLeft, [status(thm)], [c_298])).
% 2.99/1.50  tff(c_353, plain, (~v1_partfun1('#skF_5', '#skF_2') | ~v1_partfun1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_40, c_347])).
% 2.99/1.50  tff(c_364, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_211, c_213, c_353])).
% 2.99/1.50  tff(c_365, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_298])).
% 2.99/1.50  tff(c_34, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.99/1.50  tff(c_371, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_365, c_34])).
% 2.99/1.50  tff(c_381, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_176, c_371])).
% 2.99/1.50  tff(c_382, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_71])).
% 2.99/1.50  tff(c_419, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_382, c_46])).
% 2.99/1.50  tff(c_434, plain, (![B_88, A_89]: (v1_xboole_0(B_88) | ~m1_subset_1(B_88, k1_zfmisc_1(A_89)) | ~v1_xboole_0(A_89))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.99/1.50  tff(c_440, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_419, c_434])).
% 2.99/1.50  tff(c_447, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_440])).
% 2.99/1.50  tff(c_467, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_447, c_58])).
% 2.99/1.50  tff(c_474, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_467, c_419])).
% 2.99/1.50  tff(c_483, plain, (![B_5]: (k2_zfmisc_1('#skF_4', B_5)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_467, c_467, c_63])).
% 2.99/1.50  tff(c_571, plain, (![A_97, B_98, D_99]: (r2_relset_1(A_97, B_98, D_99, D_99) | ~m1_subset_1(D_99, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.99/1.50  tff(c_601, plain, (![B_105, D_106]: (r2_relset_1('#skF_4', B_105, D_106, D_106) | ~m1_subset_1(D_106, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_483, c_571])).
% 2.99/1.50  tff(c_607, plain, (![B_105]: (r2_relset_1('#skF_4', B_105, '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_474, c_601])).
% 2.99/1.50  tff(c_418, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_382, c_40])).
% 2.99/1.50  tff(c_443, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_418, c_434])).
% 2.99/1.50  tff(c_450, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_443])).
% 2.99/1.50  tff(c_471, plain, ('#skF_5'='#skF_1'), inference(resolution, [status(thm)], [c_450, c_58])).
% 2.99/1.50  tff(c_504, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_467, c_471])).
% 2.99/1.50  tff(c_383, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_71])).
% 2.99/1.50  tff(c_410, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_383, c_382, c_34])).
% 2.99/1.50  tff(c_478, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_467, c_467, c_410])).
% 2.99/1.50  tff(c_582, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_504, c_478])).
% 2.99/1.50  tff(c_611, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_607, c_582])).
% 2.99/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.50  
% 2.99/1.50  Inference rules
% 2.99/1.50  ----------------------
% 2.99/1.50  #Ref     : 0
% 2.99/1.50  #Sup     : 115
% 2.99/1.50  #Fact    : 0
% 2.99/1.50  #Define  : 0
% 2.99/1.50  #Split   : 7
% 2.99/1.50  #Chain   : 0
% 2.99/1.50  #Close   : 0
% 2.99/1.50  
% 2.99/1.50  Ordering : KBO
% 2.99/1.50  
% 2.99/1.50  Simplification rules
% 2.99/1.50  ----------------------
% 2.99/1.50  #Subsume      : 6
% 2.99/1.50  #Demod        : 128
% 2.99/1.50  #Tautology    : 79
% 2.99/1.50  #SimpNegUnit  : 4
% 2.99/1.50  #BackRed      : 30
% 2.99/1.50  
% 2.99/1.50  #Partial instantiations: 0
% 2.99/1.50  #Strategies tried      : 1
% 2.99/1.50  
% 2.99/1.50  Timing (in seconds)
% 2.99/1.50  ----------------------
% 2.99/1.50  Preprocessing        : 0.39
% 2.99/1.50  Parsing              : 0.22
% 2.99/1.50  CNF conversion       : 0.03
% 2.99/1.50  Main loop            : 0.32
% 2.99/1.50  Inferencing          : 0.11
% 2.99/1.50  Reduction            : 0.11
% 2.99/1.50  Demodulation         : 0.08
% 2.99/1.50  BG Simplification    : 0.02
% 2.99/1.50  Subsumption          : 0.05
% 2.99/1.51  Abstraction          : 0.01
% 2.99/1.51  MUC search           : 0.00
% 2.99/1.51  Cooper               : 0.00
% 2.99/1.51  Total                : 0.75
% 2.99/1.51  Index Insertion      : 0.00
% 2.99/1.51  Index Deletion       : 0.00
% 2.99/1.51  Index Matching       : 0.00
% 2.99/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
