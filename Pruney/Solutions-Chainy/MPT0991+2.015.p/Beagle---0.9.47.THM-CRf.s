%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:28 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 116 expanded)
%              Number of leaves         :   32 (  55 expanded)
%              Depth                    :    9
%              Number of atoms          :  124 ( 353 expanded)
%              Number of equality atoms :   14 (  37 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(f_126,negated_conjecture,(
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

tff(f_46,axiom,(
    ! [A] :
      ( ( v1_xboole_0(A)
        & v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_81,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_48,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_75,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_103,axiom,(
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

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(c_52,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_76,plain,(
    ! [A_34] :
      ( v2_funct_1(A_34)
      | ~ v1_funct_1(A_34)
      | ~ v1_relat_1(A_34)
      | ~ v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_36,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_79,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_36])).

tff(c_82,plain,
    ( ~ v1_relat_1('#skF_3')
    | ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_79])).

tff(c_83,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_48,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_84,plain,(
    ! [C_35,A_36,B_37] :
      ( v1_xboole_0(C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37)))
      | ~ v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_93,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_84])).

tff(c_98,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_93])).

tff(c_50,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_44,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_42,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_30,plain,(
    ! [A_20] : k6_relat_1(A_20) = k6_partfun1(A_20) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_14,plain,(
    ! [A_4] : v2_funct_1(k6_relat_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_53,plain,(
    ! [A_4] : v2_funct_1(k6_partfun1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_14])).

tff(c_211,plain,(
    ! [F_67,E_70,C_72,D_68,B_69,A_71] :
      ( m1_subset_1(k1_partfun1(A_71,B_69,C_72,D_68,E_70,F_67),k1_zfmisc_1(k2_zfmisc_1(A_71,D_68)))
      | ~ m1_subset_1(F_67,k1_zfmisc_1(k2_zfmisc_1(C_72,D_68)))
      | ~ v1_funct_1(F_67)
      | ~ m1_subset_1(E_70,k1_zfmisc_1(k2_zfmisc_1(A_71,B_69)))
      | ~ v1_funct_1(E_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_28,plain,(
    ! [A_19] : m1_subset_1(k6_partfun1(A_19),k1_zfmisc_1(k2_zfmisc_1(A_19,A_19))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_38,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_119,plain,(
    ! [D_42,C_43,A_44,B_45] :
      ( D_42 = C_43
      | ~ r2_relset_1(A_44,B_45,C_43,D_42)
      | ~ m1_subset_1(D_42,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45)))
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_125,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_38,c_119])).

tff(c_136,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_125])).

tff(c_146,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_136])).

tff(c_224,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_211,c_146])).

tff(c_237,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_44,c_40,c_224])).

tff(c_238,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_486,plain,(
    ! [E_140,A_138,C_141,B_142,D_139] :
      ( k1_xboole_0 = C_141
      | v2_funct_1(D_139)
      | ~ v2_funct_1(k1_partfun1(A_138,B_142,B_142,C_141,D_139,E_140))
      | ~ m1_subset_1(E_140,k1_zfmisc_1(k2_zfmisc_1(B_142,C_141)))
      | ~ v1_funct_2(E_140,B_142,C_141)
      | ~ v1_funct_1(E_140)
      | ~ m1_subset_1(D_139,k1_zfmisc_1(k2_zfmisc_1(A_138,B_142)))
      | ~ v1_funct_2(D_139,A_138,B_142)
      | ~ v1_funct_1(D_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_488,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_486])).

tff(c_493,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_44,c_42,c_40,c_53,c_488])).

tff(c_494,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_493])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_500,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_494,c_2])).

tff(c_503,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_500])).

tff(c_504,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_505,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_relat_1(A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_508,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_505,c_4])).

tff(c_515,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_504,c_508])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:08:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.67/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.43  
% 2.67/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.44  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.67/1.44  
% 2.67/1.44  %Foreground sorts:
% 2.67/1.44  
% 2.67/1.44  
% 2.67/1.44  %Background operators:
% 2.67/1.44  
% 2.67/1.44  
% 2.67/1.44  %Foreground operators:
% 2.67/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.67/1.44  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.67/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.67/1.44  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.67/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.67/1.44  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.67/1.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.67/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.67/1.44  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.67/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.67/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.67/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.67/1.44  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.67/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.67/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.67/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.67/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.67/1.44  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.67/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.67/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.67/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.67/1.44  
% 2.67/1.45  tff(f_126, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~((~(B = k1_xboole_0) & (?[D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))))) & ~v2_funct_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_funct_2)).
% 2.67/1.45  tff(f_46, axiom, (![A]: (((v1_xboole_0(A) & v1_relat_1(A)) & v1_funct_1(A)) => ((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_1)).
% 2.67/1.45  tff(f_55, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 2.67/1.45  tff(f_81, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.67/1.45  tff(f_48, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_funct_1)).
% 2.67/1.45  tff(f_75, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 2.67/1.45  tff(f_79, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 2.67/1.45  tff(f_63, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.67/1.45  tff(f_103, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 2.67/1.45  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.67/1.45  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.67/1.45  tff(c_52, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.67/1.45  tff(c_76, plain, (![A_34]: (v2_funct_1(A_34) | ~v1_funct_1(A_34) | ~v1_relat_1(A_34) | ~v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.67/1.45  tff(c_36, plain, (~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.67/1.45  tff(c_79, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_76, c_36])).
% 2.67/1.45  tff(c_82, plain, (~v1_relat_1('#skF_3') | ~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_79])).
% 2.67/1.45  tff(c_83, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_82])).
% 2.67/1.45  tff(c_48, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.67/1.45  tff(c_84, plain, (![C_35, A_36, B_37]: (v1_xboole_0(C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))) | ~v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.67/1.45  tff(c_93, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_48, c_84])).
% 2.67/1.45  tff(c_98, plain, (~v1_xboole_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_83, c_93])).
% 2.67/1.45  tff(c_50, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.67/1.45  tff(c_44, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.67/1.45  tff(c_42, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.67/1.45  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.67/1.45  tff(c_30, plain, (![A_20]: (k6_relat_1(A_20)=k6_partfun1(A_20))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.67/1.45  tff(c_14, plain, (![A_4]: (v2_funct_1(k6_relat_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.67/1.45  tff(c_53, plain, (![A_4]: (v2_funct_1(k6_partfun1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_14])).
% 2.67/1.45  tff(c_211, plain, (![F_67, E_70, C_72, D_68, B_69, A_71]: (m1_subset_1(k1_partfun1(A_71, B_69, C_72, D_68, E_70, F_67), k1_zfmisc_1(k2_zfmisc_1(A_71, D_68))) | ~m1_subset_1(F_67, k1_zfmisc_1(k2_zfmisc_1(C_72, D_68))) | ~v1_funct_1(F_67) | ~m1_subset_1(E_70, k1_zfmisc_1(k2_zfmisc_1(A_71, B_69))) | ~v1_funct_1(E_70))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.67/1.45  tff(c_28, plain, (![A_19]: (m1_subset_1(k6_partfun1(A_19), k1_zfmisc_1(k2_zfmisc_1(A_19, A_19))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.67/1.45  tff(c_38, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.67/1.45  tff(c_119, plain, (![D_42, C_43, A_44, B_45]: (D_42=C_43 | ~r2_relset_1(A_44, B_45, C_43, D_42) | ~m1_subset_1(D_42, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.67/1.45  tff(c_125, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_38, c_119])).
% 2.67/1.45  tff(c_136, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_125])).
% 2.67/1.45  tff(c_146, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_136])).
% 2.67/1.45  tff(c_224, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_211, c_146])).
% 2.67/1.45  tff(c_237, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_44, c_40, c_224])).
% 2.67/1.45  tff(c_238, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_136])).
% 2.67/1.45  tff(c_486, plain, (![E_140, A_138, C_141, B_142, D_139]: (k1_xboole_0=C_141 | v2_funct_1(D_139) | ~v2_funct_1(k1_partfun1(A_138, B_142, B_142, C_141, D_139, E_140)) | ~m1_subset_1(E_140, k1_zfmisc_1(k2_zfmisc_1(B_142, C_141))) | ~v1_funct_2(E_140, B_142, C_141) | ~v1_funct_1(E_140) | ~m1_subset_1(D_139, k1_zfmisc_1(k2_zfmisc_1(A_138, B_142))) | ~v1_funct_2(D_139, A_138, B_142) | ~v1_funct_1(D_139))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.67/1.45  tff(c_488, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_238, c_486])).
% 2.67/1.45  tff(c_493, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_44, c_42, c_40, c_53, c_488])).
% 2.67/1.45  tff(c_494, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_36, c_493])).
% 2.67/1.45  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.67/1.45  tff(c_500, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_494, c_2])).
% 2.67/1.45  tff(c_503, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_500])).
% 2.67/1.45  tff(c_504, plain, (~v1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_82])).
% 2.67/1.45  tff(c_505, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_82])).
% 2.67/1.45  tff(c_4, plain, (![A_1]: (v1_relat_1(A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.67/1.45  tff(c_508, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_505, c_4])).
% 2.67/1.45  tff(c_515, plain, $false, inference(negUnitSimplification, [status(thm)], [c_504, c_508])).
% 2.67/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.45  
% 2.67/1.45  Inference rules
% 2.67/1.45  ----------------------
% 2.67/1.45  #Ref     : 0
% 2.67/1.45  #Sup     : 92
% 2.67/1.45  #Fact    : 0
% 2.67/1.45  #Define  : 0
% 2.67/1.45  #Split   : 3
% 2.67/1.45  #Chain   : 0
% 2.67/1.45  #Close   : 0
% 2.67/1.45  
% 2.67/1.45  Ordering : KBO
% 2.67/1.45  
% 2.67/1.45  Simplification rules
% 2.67/1.45  ----------------------
% 2.67/1.45  #Subsume      : 9
% 2.67/1.45  #Demod        : 71
% 2.67/1.45  #Tautology    : 12
% 2.67/1.45  #SimpNegUnit  : 4
% 2.67/1.45  #BackRed      : 7
% 2.67/1.45  
% 2.67/1.45  #Partial instantiations: 0
% 2.67/1.45  #Strategies tried      : 1
% 2.67/1.45  
% 2.67/1.45  Timing (in seconds)
% 2.67/1.45  ----------------------
% 2.67/1.45  Preprocessing        : 0.32
% 2.67/1.45  Parsing              : 0.17
% 2.67/1.45  CNF conversion       : 0.02
% 2.67/1.45  Main loop            : 0.32
% 2.67/1.45  Inferencing          : 0.12
% 2.67/1.45  Reduction            : 0.10
% 2.67/1.45  Demodulation         : 0.07
% 2.67/1.45  BG Simplification    : 0.02
% 2.67/1.45  Subsumption          : 0.06
% 2.67/1.45  Abstraction          : 0.01
% 2.67/1.45  MUC search           : 0.00
% 2.67/1.45  Cooper               : 0.00
% 2.67/1.45  Total                : 0.67
% 2.67/1.45  Index Insertion      : 0.00
% 2.67/1.45  Index Deletion       : 0.00
% 2.67/1.45  Index Matching       : 0.00
% 2.67/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
