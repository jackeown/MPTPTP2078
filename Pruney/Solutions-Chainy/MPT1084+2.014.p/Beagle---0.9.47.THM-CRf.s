%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:21 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 365 expanded)
%              Number of leaves         :   30 ( 151 expanded)
%              Depth                    :   11
%              Number of atoms          :  129 (1105 expanded)
%              Number of equality atoms :   38 ( 249 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_107,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( v1_funct_1(B)
              & v1_funct_2(B,A,A)
              & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( ! [C] :
                  ( m1_subset_1(C,A)
                 => k3_funct_2(A,A,B,C) = C )
             => r2_funct_2(A,A,B,k6_partfun1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t201_funct_2)).

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_funct_2(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_65,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(c_34,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_32,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_73,plain,(
    ! [A_44,B_45,D_46] :
      ( r2_funct_2(A_44,B_45,D_46,D_46)
      | ~ m1_subset_1(D_46,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45)))
      | ~ v1_funct_2(D_46,A_44,B_45)
      | ~ v1_funct_1(D_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_75,plain,
    ( r2_funct_2('#skF_2','#skF_2','#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_73])).

tff(c_78,plain,(
    r2_funct_2('#skF_2','#skF_2','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_75])).

tff(c_51,plain,(
    ! [C_33,A_34,B_35] :
      ( v1_relat_1(C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_55,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_51])).

tff(c_58,plain,(
    ! [A_38,B_39,C_40] :
      ( k1_relset_1(A_38,B_39,C_40) = k1_relat_1(C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_62,plain,(
    k1_relset_1('#skF_2','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_58])).

tff(c_80,plain,(
    ! [A_48,B_49] :
      ( k1_relset_1(A_48,A_48,B_49) = A_48
      | ~ m1_subset_1(B_49,k1_zfmisc_1(k2_zfmisc_1(A_48,A_48)))
      | ~ v1_funct_2(B_49,A_48,A_48)
      | ~ v1_funct_1(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_83,plain,
    ( k1_relset_1('#skF_2','#skF_2','#skF_3') = '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_80])).

tff(c_86,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_62,c_83])).

tff(c_18,plain,(
    ! [A_18] : k6_relat_1(A_18) = k6_partfun1(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6,plain,(
    ! [B_4] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_4),B_4),k1_relat_1(B_4))
      | k6_relat_1(k1_relat_1(B_4)) = B_4
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_68,plain,(
    ! [B_43] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_43),B_43),k1_relat_1(B_43))
      | k6_partfun1(k1_relat_1(B_43)) = B_43
      | ~ v1_funct_1(B_43)
      | ~ v1_relat_1(B_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_6])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_72,plain,(
    ! [B_43] :
      ( m1_subset_1('#skF_1'(k1_relat_1(B_43),B_43),k1_relat_1(B_43))
      | k6_partfun1(k1_relat_1(B_43)) = B_43
      | ~ v1_funct_1(B_43)
      | ~ v1_relat_1(B_43) ) ),
    inference(resolution,[status(thm)],[c_68,c_2])).

tff(c_91,plain,
    ( m1_subset_1('#skF_1'('#skF_2','#skF_3'),k1_relat_1('#skF_3'))
    | k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_72])).

tff(c_104,plain,
    ( m1_subset_1('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | k6_partfun1('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_34,c_86,c_86,c_91])).

tff(c_116,plain,(
    k6_partfun1('#skF_2') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_104])).

tff(c_26,plain,(
    ~ r2_funct_2('#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_117,plain,(
    ~ r2_funct_2('#skF_2','#skF_2','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_26])).

tff(c_120,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_117])).

tff(c_122,plain,(
    k6_partfun1('#skF_2') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_4,plain,(
    ! [B_4] :
      ( k1_funct_1(B_4,'#skF_1'(k1_relat_1(B_4),B_4)) != '#skF_1'(k1_relat_1(B_4),B_4)
      | k6_relat_1(k1_relat_1(B_4)) = B_4
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_127,plain,(
    ! [B_50] :
      ( k1_funct_1(B_50,'#skF_1'(k1_relat_1(B_50),B_50)) != '#skF_1'(k1_relat_1(B_50),B_50)
      | k6_partfun1(k1_relat_1(B_50)) = B_50
      | ~ v1_funct_1(B_50)
      | ~ v1_relat_1(B_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_4])).

tff(c_130,plain,
    ( k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) != '#skF_1'(k1_relat_1('#skF_3'),'#skF_3')
    | k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_127])).

tff(c_132,plain,
    ( k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) != '#skF_1'('#skF_2','#skF_3')
    | k6_partfun1('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_34,c_86,c_86,c_130])).

tff(c_133,plain,(
    k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) != '#skF_1'('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_132])).

tff(c_121,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_28,plain,(
    ! [C_29] :
      ( k3_funct_2('#skF_2','#skF_2','#skF_3',C_29) = C_29
      | ~ m1_subset_1(C_29,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_126,plain,(
    k3_funct_2('#skF_2','#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3')) = '#skF_1'('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_121,c_28])).

tff(c_36,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_148,plain,(
    ! [A_51,B_52,C_53,D_54] :
      ( k3_funct_2(A_51,B_52,C_53,D_54) = k1_funct_1(C_53,D_54)
      | ~ m1_subset_1(D_54,A_51)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52)))
      | ~ v1_funct_2(C_53,A_51,B_52)
      | ~ v1_funct_1(C_53)
      | v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_150,plain,(
    ! [B_52,C_53] :
      ( k3_funct_2('#skF_2',B_52,C_53,'#skF_1'('#skF_2','#skF_3')) = k1_funct_1(C_53,'#skF_1'('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_52)))
      | ~ v1_funct_2(C_53,'#skF_2',B_52)
      | ~ v1_funct_1(C_53)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_121,c_148])).

tff(c_160,plain,(
    ! [B_55,C_56] :
      ( k3_funct_2('#skF_2',B_55,C_56,'#skF_1'('#skF_2','#skF_3')) = k1_funct_1(C_56,'#skF_1'('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_55)))
      | ~ v1_funct_2(C_56,'#skF_2',B_55)
      | ~ v1_funct_1(C_56) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_150])).

tff(c_163,plain,
    ( k3_funct_2('#skF_2','#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3')) = k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3'))
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_160])).

tff(c_166,plain,(
    k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) = '#skF_1'('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_126,c_163])).

tff(c_168,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_166])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:01:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.25  
% 2.21/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.25  %$ r2_funct_2 > v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.21/1.25  
% 2.21/1.25  %Foreground sorts:
% 2.21/1.25  
% 2.21/1.25  
% 2.21/1.25  %Background operators:
% 2.21/1.25  
% 2.21/1.25  
% 2.21/1.25  %Foreground operators:
% 2.21/1.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.21/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.21/1.25  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.21/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.21/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.21/1.25  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.21/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.21/1.25  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.21/1.25  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.21/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.21/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.21/1.25  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.21/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.21/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.21/1.25  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.21/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.21/1.25  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 2.21/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.21/1.25  
% 2.21/1.27  tff(f_107, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => ((![C]: (m1_subset_1(C, A) => (k3_funct_2(A, A, B, C) = C))) => r2_funct_2(A, A, B, k6_partfun1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t201_funct_2)).
% 2.21/1.27  tff(f_81, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 2.21/1.27  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.21/1.27  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.21/1.27  tff(f_89, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_2)).
% 2.21/1.27  tff(f_65, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.21/1.27  tff(f_42, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_funct_1)).
% 2.21/1.27  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 2.21/1.27  tff(f_63, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.21/1.27  tff(c_34, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.21/1.27  tff(c_32, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.21/1.27  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.21/1.27  tff(c_73, plain, (![A_44, B_45, D_46]: (r2_funct_2(A_44, B_45, D_46, D_46) | ~m1_subset_1(D_46, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))) | ~v1_funct_2(D_46, A_44, B_45) | ~v1_funct_1(D_46))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.21/1.27  tff(c_75, plain, (r2_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_73])).
% 2.21/1.27  tff(c_78, plain, (r2_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_75])).
% 2.21/1.27  tff(c_51, plain, (![C_33, A_34, B_35]: (v1_relat_1(C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.21/1.27  tff(c_55, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_51])).
% 2.21/1.27  tff(c_58, plain, (![A_38, B_39, C_40]: (k1_relset_1(A_38, B_39, C_40)=k1_relat_1(C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.21/1.27  tff(c_62, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_58])).
% 2.21/1.27  tff(c_80, plain, (![A_48, B_49]: (k1_relset_1(A_48, A_48, B_49)=A_48 | ~m1_subset_1(B_49, k1_zfmisc_1(k2_zfmisc_1(A_48, A_48))) | ~v1_funct_2(B_49, A_48, A_48) | ~v1_funct_1(B_49))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.21/1.27  tff(c_83, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')='#skF_2' | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_80])).
% 2.21/1.27  tff(c_86, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_62, c_83])).
% 2.21/1.27  tff(c_18, plain, (![A_18]: (k6_relat_1(A_18)=k6_partfun1(A_18))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.21/1.27  tff(c_6, plain, (![B_4]: (r2_hidden('#skF_1'(k1_relat_1(B_4), B_4), k1_relat_1(B_4)) | k6_relat_1(k1_relat_1(B_4))=B_4 | ~v1_funct_1(B_4) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.21/1.27  tff(c_68, plain, (![B_43]: (r2_hidden('#skF_1'(k1_relat_1(B_43), B_43), k1_relat_1(B_43)) | k6_partfun1(k1_relat_1(B_43))=B_43 | ~v1_funct_1(B_43) | ~v1_relat_1(B_43))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_6])).
% 2.21/1.27  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.21/1.27  tff(c_72, plain, (![B_43]: (m1_subset_1('#skF_1'(k1_relat_1(B_43), B_43), k1_relat_1(B_43)) | k6_partfun1(k1_relat_1(B_43))=B_43 | ~v1_funct_1(B_43) | ~v1_relat_1(B_43))), inference(resolution, [status(thm)], [c_68, c_2])).
% 2.21/1.27  tff(c_91, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3'), k1_relat_1('#skF_3')) | k6_partfun1(k1_relat_1('#skF_3'))='#skF_3' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_86, c_72])).
% 2.21/1.27  tff(c_104, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | k6_partfun1('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_55, c_34, c_86, c_86, c_91])).
% 2.21/1.27  tff(c_116, plain, (k6_partfun1('#skF_2')='#skF_3'), inference(splitLeft, [status(thm)], [c_104])).
% 2.21/1.27  tff(c_26, plain, (~r2_funct_2('#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.21/1.27  tff(c_117, plain, (~r2_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_116, c_26])).
% 2.21/1.27  tff(c_120, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_117])).
% 2.21/1.27  tff(c_122, plain, (k6_partfun1('#skF_2')!='#skF_3'), inference(splitRight, [status(thm)], [c_104])).
% 2.21/1.27  tff(c_4, plain, (![B_4]: (k1_funct_1(B_4, '#skF_1'(k1_relat_1(B_4), B_4))!='#skF_1'(k1_relat_1(B_4), B_4) | k6_relat_1(k1_relat_1(B_4))=B_4 | ~v1_funct_1(B_4) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.21/1.27  tff(c_127, plain, (![B_50]: (k1_funct_1(B_50, '#skF_1'(k1_relat_1(B_50), B_50))!='#skF_1'(k1_relat_1(B_50), B_50) | k6_partfun1(k1_relat_1(B_50))=B_50 | ~v1_funct_1(B_50) | ~v1_relat_1(B_50))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_4])).
% 2.21/1.27  tff(c_130, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))!='#skF_1'(k1_relat_1('#skF_3'), '#skF_3') | k6_partfun1(k1_relat_1('#skF_3'))='#skF_3' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_86, c_127])).
% 2.21/1.27  tff(c_132, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))!='#skF_1'('#skF_2', '#skF_3') | k6_partfun1('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_55, c_34, c_86, c_86, c_130])).
% 2.21/1.27  tff(c_133, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))!='#skF_1'('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_122, c_132])).
% 2.21/1.27  tff(c_121, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_104])).
% 2.21/1.27  tff(c_28, plain, (![C_29]: (k3_funct_2('#skF_2', '#skF_2', '#skF_3', C_29)=C_29 | ~m1_subset_1(C_29, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.21/1.27  tff(c_126, plain, (k3_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3'))='#skF_1'('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_121, c_28])).
% 2.21/1.27  tff(c_36, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.21/1.27  tff(c_148, plain, (![A_51, B_52, C_53, D_54]: (k3_funct_2(A_51, B_52, C_53, D_54)=k1_funct_1(C_53, D_54) | ~m1_subset_1(D_54, A_51) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))) | ~v1_funct_2(C_53, A_51, B_52) | ~v1_funct_1(C_53) | v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.21/1.27  tff(c_150, plain, (![B_52, C_53]: (k3_funct_2('#skF_2', B_52, C_53, '#skF_1'('#skF_2', '#skF_3'))=k1_funct_1(C_53, '#skF_1'('#skF_2', '#skF_3')) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_52))) | ~v1_funct_2(C_53, '#skF_2', B_52) | ~v1_funct_1(C_53) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_121, c_148])).
% 2.21/1.27  tff(c_160, plain, (![B_55, C_56]: (k3_funct_2('#skF_2', B_55, C_56, '#skF_1'('#skF_2', '#skF_3'))=k1_funct_1(C_56, '#skF_1'('#skF_2', '#skF_3')) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_55))) | ~v1_funct_2(C_56, '#skF_2', B_55) | ~v1_funct_1(C_56))), inference(negUnitSimplification, [status(thm)], [c_36, c_150])).
% 2.21/1.27  tff(c_163, plain, (k3_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3'))=k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3')) | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_160])).
% 2.21/1.27  tff(c_166, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))='#skF_1'('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_126, c_163])).
% 2.21/1.27  tff(c_168, plain, $false, inference(negUnitSimplification, [status(thm)], [c_133, c_166])).
% 2.21/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.27  
% 2.21/1.27  Inference rules
% 2.21/1.27  ----------------------
% 2.21/1.27  #Ref     : 0
% 2.21/1.27  #Sup     : 26
% 2.21/1.27  #Fact    : 0
% 2.21/1.27  #Define  : 0
% 2.21/1.27  #Split   : 1
% 2.21/1.27  #Chain   : 0
% 2.21/1.27  #Close   : 0
% 2.21/1.27  
% 2.21/1.27  Ordering : KBO
% 2.21/1.27  
% 2.21/1.27  Simplification rules
% 2.21/1.27  ----------------------
% 2.21/1.27  #Subsume      : 0
% 2.21/1.27  #Demod        : 42
% 2.21/1.27  #Tautology    : 13
% 2.21/1.27  #SimpNegUnit  : 6
% 2.21/1.27  #BackRed      : 2
% 2.21/1.27  
% 2.21/1.27  #Partial instantiations: 0
% 2.21/1.27  #Strategies tried      : 1
% 2.21/1.27  
% 2.21/1.27  Timing (in seconds)
% 2.21/1.27  ----------------------
% 2.21/1.27  Preprocessing        : 0.33
% 2.21/1.27  Parsing              : 0.17
% 2.21/1.27  CNF conversion       : 0.02
% 2.21/1.27  Main loop            : 0.17
% 2.21/1.27  Inferencing          : 0.06
% 2.21/1.27  Reduction            : 0.06
% 2.21/1.27  Demodulation         : 0.04
% 2.21/1.27  BG Simplification    : 0.01
% 2.21/1.27  Subsumption          : 0.02
% 2.21/1.27  Abstraction          : 0.01
% 2.21/1.27  MUC search           : 0.00
% 2.21/1.27  Cooper               : 0.00
% 2.21/1.27  Total                : 0.53
% 2.21/1.27  Index Insertion      : 0.00
% 2.21/1.27  Index Deletion       : 0.00
% 2.21/1.27  Index Matching       : 0.00
% 2.21/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
