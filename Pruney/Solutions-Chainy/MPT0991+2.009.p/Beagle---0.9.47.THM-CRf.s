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
% DateTime   : Thu Dec  3 10:13:27 EST 2020

% Result     : Theorem 2.88s
% Output     : CNFRefutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 124 expanded)
%              Number of leaves         :   32 (  57 expanded)
%              Depth                    :    9
%              Number of atoms          :  130 ( 363 expanded)
%              Number of equality atoms :   14 (  41 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_30,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_130,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ~ ( B != k1_xboole_0
            & ? [D] :
                ( v1_funct_1(D)
                & v1_funct_2(D,B,A)
                & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A)))
                & r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A)) )
            & ~ v2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_funct_2)).

tff(f_57,axiom,(
    ! [A] :
      ( ( v1_xboole_0(A)
        & v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_85,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_83,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_71,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_107,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | v2_funct_1(D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( v1_xboole_0(k2_zfmisc_1(A_1,B_2))
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_54,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_91,plain,(
    ! [A_41] :
      ( v2_funct_1(A_41)
      | ~ v1_funct_1(A_41)
      | ~ v1_relat_1(A_41)
      | ~ v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_38,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_94,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_91,c_38])).

tff(c_97,plain,
    ( ~ v1_relat_1('#skF_3')
    | ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_94])).

tff(c_98,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_97])).

tff(c_50,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_99,plain,(
    ! [B_42,A_43] :
      ( v1_xboole_0(B_42)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_43))
      | ~ v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_108,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_50,c_99])).

tff(c_113,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_108])).

tff(c_127,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_113])).

tff(c_52,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_46,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_44,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_32,plain,(
    ! [A_21] : k6_relat_1(A_21) = k6_partfun1(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_20,plain,(
    ! [A_9] : v2_funct_1(k6_relat_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_56,plain,(
    ! [A_9] : v2_funct_1(k6_partfun1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_20])).

tff(c_208,plain,(
    ! [D_66,F_68,B_67,A_70,C_65,E_69] :
      ( m1_subset_1(k1_partfun1(A_70,B_67,C_65,D_66,E_69,F_68),k1_zfmisc_1(k2_zfmisc_1(A_70,D_66)))
      | ~ m1_subset_1(F_68,k1_zfmisc_1(k2_zfmisc_1(C_65,D_66)))
      | ~ v1_funct_1(F_68)
      | ~ m1_subset_1(E_69,k1_zfmisc_1(k2_zfmisc_1(A_70,B_67)))
      | ~ v1_funct_1(E_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_26,plain,(
    ! [A_14] : m1_subset_1(k6_relat_1(A_14),k1_zfmisc_1(k2_zfmisc_1(A_14,A_14))) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_55,plain,(
    ! [A_14] : m1_subset_1(k6_partfun1(A_14),k1_zfmisc_1(k2_zfmisc_1(A_14,A_14))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_26])).

tff(c_40,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_149,plain,(
    ! [D_49,C_50,A_51,B_52] :
      ( D_49 = C_50
      | ~ r2_relset_1(A_51,B_52,C_50,D_49)
      | ~ m1_subset_1(D_49,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52)))
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_155,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_40,c_149])).

tff(c_166,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_155])).

tff(c_175,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_166])).

tff(c_216,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_208,c_175])).

tff(c_227,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_46,c_42,c_216])).

tff(c_228,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_166])).

tff(c_455,plain,(
    ! [B_129,E_126,C_127,A_125,D_128] :
      ( k1_xboole_0 = C_127
      | v2_funct_1(D_128)
      | ~ v2_funct_1(k1_partfun1(A_125,B_129,B_129,C_127,D_128,E_126))
      | ~ m1_subset_1(E_126,k1_zfmisc_1(k2_zfmisc_1(B_129,C_127)))
      | ~ v1_funct_2(E_126,B_129,C_127)
      | ~ v1_funct_1(E_126)
      | ~ m1_subset_1(D_128,k1_zfmisc_1(k2_zfmisc_1(A_125,B_129)))
      | ~ v1_funct_2(D_128,A_125,B_129)
      | ~ v1_funct_1(D_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_457,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_455])).

tff(c_462,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_46,c_44,c_42,c_56,c_457])).

tff(c_463,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_462])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_469,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_463,c_2])).

tff(c_472,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_469])).

tff(c_473,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_97])).

tff(c_474,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_97])).

tff(c_8,plain,(
    ! [A_6] :
      ( v1_relat_1(A_6)
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_480,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_474,c_8])).

tff(c_486,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_473,c_480])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:16:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.88/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.41  
% 2.88/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.41  %$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.88/1.41  
% 2.88/1.41  %Foreground sorts:
% 2.88/1.41  
% 2.88/1.41  
% 2.88/1.41  %Background operators:
% 2.88/1.41  
% 2.88/1.41  
% 2.88/1.41  %Foreground operators:
% 2.88/1.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.88/1.41  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.88/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.88/1.41  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.88/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.88/1.41  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.88/1.41  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.88/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.88/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.88/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.88/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.88/1.41  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.88/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.88/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.88/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.88/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.88/1.41  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.88/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.88/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.88/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.88/1.41  
% 2.88/1.42  tff(f_30, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 2.88/1.42  tff(f_130, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~((~(B = k1_xboole_0) & (?[D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))))) & ~v2_funct_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_funct_2)).
% 2.88/1.42  tff(f_57, axiom, (![A]: (((v1_xboole_0(A) & v1_relat_1(A)) & v1_funct_1(A)) => ((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_1)).
% 2.88/1.42  tff(f_37, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.88/1.42  tff(f_85, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.88/1.42  tff(f_61, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 2.88/1.42  tff(f_83, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 2.88/1.42  tff(f_71, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 2.88/1.42  tff(f_69, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.88/1.42  tff(f_107, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 2.88/1.42  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.88/1.42  tff(f_41, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.88/1.42  tff(c_4, plain, (![A_1, B_2]: (v1_xboole_0(k2_zfmisc_1(A_1, B_2)) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.88/1.42  tff(c_54, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.88/1.42  tff(c_91, plain, (![A_41]: (v2_funct_1(A_41) | ~v1_funct_1(A_41) | ~v1_relat_1(A_41) | ~v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.88/1.42  tff(c_38, plain, (~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.88/1.42  tff(c_94, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_91, c_38])).
% 2.88/1.42  tff(c_97, plain, (~v1_relat_1('#skF_3') | ~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_94])).
% 2.88/1.42  tff(c_98, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_97])).
% 2.88/1.42  tff(c_50, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.88/1.42  tff(c_99, plain, (![B_42, A_43]: (v1_xboole_0(B_42) | ~m1_subset_1(B_42, k1_zfmisc_1(A_43)) | ~v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.88/1.42  tff(c_108, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_50, c_99])).
% 2.88/1.42  tff(c_113, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_98, c_108])).
% 2.88/1.42  tff(c_127, plain, (~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_4, c_113])).
% 2.88/1.42  tff(c_52, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.88/1.42  tff(c_46, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.88/1.42  tff(c_44, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.88/1.42  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.88/1.42  tff(c_32, plain, (![A_21]: (k6_relat_1(A_21)=k6_partfun1(A_21))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.88/1.42  tff(c_20, plain, (![A_9]: (v2_funct_1(k6_relat_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.88/1.42  tff(c_56, plain, (![A_9]: (v2_funct_1(k6_partfun1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_20])).
% 2.88/1.42  tff(c_208, plain, (![D_66, F_68, B_67, A_70, C_65, E_69]: (m1_subset_1(k1_partfun1(A_70, B_67, C_65, D_66, E_69, F_68), k1_zfmisc_1(k2_zfmisc_1(A_70, D_66))) | ~m1_subset_1(F_68, k1_zfmisc_1(k2_zfmisc_1(C_65, D_66))) | ~v1_funct_1(F_68) | ~m1_subset_1(E_69, k1_zfmisc_1(k2_zfmisc_1(A_70, B_67))) | ~v1_funct_1(E_69))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.88/1.42  tff(c_26, plain, (![A_14]: (m1_subset_1(k6_relat_1(A_14), k1_zfmisc_1(k2_zfmisc_1(A_14, A_14))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.88/1.42  tff(c_55, plain, (![A_14]: (m1_subset_1(k6_partfun1(A_14), k1_zfmisc_1(k2_zfmisc_1(A_14, A_14))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_26])).
% 2.88/1.42  tff(c_40, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.88/1.42  tff(c_149, plain, (![D_49, C_50, A_51, B_52]: (D_49=C_50 | ~r2_relset_1(A_51, B_52, C_50, D_49) | ~m1_subset_1(D_49, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.88/1.42  tff(c_155, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_40, c_149])).
% 2.88/1.42  tff(c_166, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_155])).
% 2.88/1.42  tff(c_175, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_166])).
% 2.88/1.42  tff(c_216, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_208, c_175])).
% 2.88/1.42  tff(c_227, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_46, c_42, c_216])).
% 2.88/1.42  tff(c_228, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_166])).
% 2.88/1.42  tff(c_455, plain, (![B_129, E_126, C_127, A_125, D_128]: (k1_xboole_0=C_127 | v2_funct_1(D_128) | ~v2_funct_1(k1_partfun1(A_125, B_129, B_129, C_127, D_128, E_126)) | ~m1_subset_1(E_126, k1_zfmisc_1(k2_zfmisc_1(B_129, C_127))) | ~v1_funct_2(E_126, B_129, C_127) | ~v1_funct_1(E_126) | ~m1_subset_1(D_128, k1_zfmisc_1(k2_zfmisc_1(A_125, B_129))) | ~v1_funct_2(D_128, A_125, B_129) | ~v1_funct_1(D_128))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.88/1.42  tff(c_457, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_228, c_455])).
% 2.88/1.42  tff(c_462, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_46, c_44, c_42, c_56, c_457])).
% 2.88/1.42  tff(c_463, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_38, c_462])).
% 2.88/1.42  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.88/1.42  tff(c_469, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_463, c_2])).
% 2.88/1.42  tff(c_472, plain, $false, inference(negUnitSimplification, [status(thm)], [c_127, c_469])).
% 2.88/1.42  tff(c_473, plain, (~v1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_97])).
% 2.88/1.42  tff(c_474, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_97])).
% 2.88/1.42  tff(c_8, plain, (![A_6]: (v1_relat_1(A_6) | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.88/1.42  tff(c_480, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_474, c_8])).
% 2.88/1.42  tff(c_486, plain, $false, inference(negUnitSimplification, [status(thm)], [c_473, c_480])).
% 2.88/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.42  
% 2.88/1.42  Inference rules
% 2.88/1.42  ----------------------
% 2.88/1.42  #Ref     : 0
% 2.88/1.42  #Sup     : 84
% 2.88/1.42  #Fact    : 0
% 2.88/1.42  #Define  : 0
% 2.88/1.42  #Split   : 4
% 2.88/1.42  #Chain   : 0
% 2.88/1.42  #Close   : 0
% 2.88/1.42  
% 2.88/1.42  Ordering : KBO
% 2.88/1.42  
% 2.88/1.42  Simplification rules
% 2.88/1.42  ----------------------
% 2.88/1.42  #Subsume      : 8
% 2.88/1.42  #Demod        : 63
% 2.88/1.42  #Tautology    : 14
% 2.88/1.42  #SimpNegUnit  : 4
% 2.88/1.42  #BackRed      : 7
% 2.88/1.42  
% 2.88/1.42  #Partial instantiations: 0
% 2.88/1.42  #Strategies tried      : 1
% 2.88/1.42  
% 2.88/1.42  Timing (in seconds)
% 2.88/1.42  ----------------------
% 2.88/1.43  Preprocessing        : 0.32
% 2.88/1.43  Parsing              : 0.17
% 2.88/1.43  CNF conversion       : 0.02
% 2.88/1.43  Main loop            : 0.31
% 2.88/1.43  Inferencing          : 0.12
% 2.88/1.43  Reduction            : 0.09
% 2.88/1.43  Demodulation         : 0.07
% 2.88/1.43  BG Simplification    : 0.02
% 2.88/1.43  Subsumption          : 0.06
% 2.88/1.43  Abstraction          : 0.01
% 2.88/1.43  MUC search           : 0.00
% 2.88/1.43  Cooper               : 0.00
% 2.88/1.43  Total                : 0.66
% 2.88/1.43  Index Insertion      : 0.00
% 2.88/1.43  Index Deletion       : 0.00
% 2.88/1.43  Index Matching       : 0.00
% 2.88/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
