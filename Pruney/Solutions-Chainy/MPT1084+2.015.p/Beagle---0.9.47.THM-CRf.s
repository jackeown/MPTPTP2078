%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:21 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 488 expanded)
%              Number of leaves         :   30 ( 198 expanded)
%              Depth                    :   12
%              Number of atoms          :  146 (1502 expanded)
%              Number of equality atoms :   39 ( 337 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

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

tff(f_105,negated_conjecture,(
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

tff(f_87,axiom,(
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

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_funct_2(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

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

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_49,plain,(
    ! [C_33,A_34,B_35] :
      ( v1_relat_1(C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_53,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_49])).

tff(c_32,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_30,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_56,plain,(
    ! [A_38,B_39,C_40] :
      ( k1_relset_1(A_38,B_39,C_40) = k1_relat_1(C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_60,plain,(
    k1_relset_1('#skF_2','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_56])).

tff(c_71,plain,(
    ! [A_44,B_45] :
      ( k1_relset_1(A_44,A_44,B_45) = A_44
      | ~ m1_subset_1(B_45,k1_zfmisc_1(k2_zfmisc_1(A_44,A_44)))
      | ~ v1_funct_2(B_45,A_44,A_44)
      | ~ v1_funct_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_74,plain,
    ( k1_relset_1('#skF_2','#skF_2','#skF_3') = '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_71])).

tff(c_77,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_60,c_74])).

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

tff(c_37,plain,(
    ! [B_4] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_4),B_4),k1_relat_1(B_4))
      | k6_partfun1(k1_relat_1(B_4)) = B_4
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_6])).

tff(c_85,plain,
    ( r2_hidden('#skF_1'(k1_relat_1('#skF_3'),'#skF_3'),'#skF_2')
    | k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_37])).

tff(c_91,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | k6_partfun1('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_32,c_77,c_77,c_85])).

tff(c_97,plain,(
    k6_partfun1('#skF_2') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_91])).

tff(c_24,plain,(
    ~ r2_funct_2('#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_99,plain,(
    ~ r2_funct_2('#skF_2','#skF_2','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_24])).

tff(c_139,plain,(
    ! [A_53,B_54,C_55,D_56] :
      ( r2_funct_2(A_53,B_54,C_55,C_55)
      | ~ m1_subset_1(D_56,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54)))
      | ~ v1_funct_2(D_56,A_53,B_54)
      | ~ v1_funct_1(D_56)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54)))
      | ~ v1_funct_2(C_55,A_53,B_54)
      | ~ v1_funct_1(C_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_141,plain,(
    ! [C_55] :
      ( r2_funct_2('#skF_2','#skF_2',C_55,C_55)
      | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
      | ~ v1_funct_2(C_55,'#skF_2','#skF_2')
      | ~ v1_funct_1(C_55) ) ),
    inference(resolution,[status(thm)],[c_28,c_139])).

tff(c_145,plain,(
    ! [C_57] :
      ( r2_funct_2('#skF_2','#skF_2',C_57,C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
      | ~ v1_funct_2(C_57,'#skF_2','#skF_2')
      | ~ v1_funct_1(C_57) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_141])).

tff(c_147,plain,
    ( r2_funct_2('#skF_2','#skF_2','#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_145])).

tff(c_150,plain,(
    r2_funct_2('#skF_2','#skF_2','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_147])).

tff(c_152,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_150])).

tff(c_154,plain,(
    k6_partfun1('#skF_2') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_91])).

tff(c_4,plain,(
    ! [B_4] :
      ( k1_funct_1(B_4,'#skF_1'(k1_relat_1(B_4),B_4)) != '#skF_1'(k1_relat_1(B_4),B_4)
      | k6_relat_1(k1_relat_1(B_4)) = B_4
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_163,plain,(
    ! [B_58] :
      ( k1_funct_1(B_58,'#skF_1'(k1_relat_1(B_58),B_58)) != '#skF_1'(k1_relat_1(B_58),B_58)
      | k6_partfun1(k1_relat_1(B_58)) = B_58
      | ~ v1_funct_1(B_58)
      | ~ v1_relat_1(B_58) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_4])).

tff(c_166,plain,
    ( k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) != '#skF_1'(k1_relat_1('#skF_3'),'#skF_3')
    | k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_163])).

tff(c_168,plain,
    ( k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) != '#skF_1'('#skF_2','#skF_3')
    | k6_partfun1('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_32,c_77,c_77,c_166])).

tff(c_169,plain,(
    k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) != '#skF_1'('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_154,c_168])).

tff(c_82,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),k1_relat_1('#skF_3'))
    | k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_37])).

tff(c_89,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | k6_partfun1('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_32,c_77,c_77,c_82])).

tff(c_155,plain,(
    k6_partfun1('#skF_2') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_89])).

tff(c_156,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_154,c_155])).

tff(c_157,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_162,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_157,c_2])).

tff(c_26,plain,(
    ! [C_29] :
      ( k3_funct_2('#skF_2','#skF_2','#skF_3',C_29) = C_29
      | ~ m1_subset_1(C_29,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_174,plain,(
    k3_funct_2('#skF_2','#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3')) = '#skF_1'('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_162,c_26])).

tff(c_34,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_192,plain,(
    ! [A_60,B_61,C_62,D_63] :
      ( k3_funct_2(A_60,B_61,C_62,D_63) = k1_funct_1(C_62,D_63)
      | ~ m1_subset_1(D_63,A_60)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61)))
      | ~ v1_funct_2(C_62,A_60,B_61)
      | ~ v1_funct_1(C_62)
      | v1_xboole_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_196,plain,(
    ! [B_61,C_62] :
      ( k3_funct_2('#skF_2',B_61,C_62,'#skF_1'('#skF_2','#skF_3')) = k1_funct_1(C_62,'#skF_1'('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_61)))
      | ~ v1_funct_2(C_62,'#skF_2',B_61)
      | ~ v1_funct_1(C_62)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_162,c_192])).

tff(c_204,plain,(
    ! [B_64,C_65] :
      ( k3_funct_2('#skF_2',B_64,C_65,'#skF_1'('#skF_2','#skF_3')) = k1_funct_1(C_65,'#skF_1'('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_64)))
      | ~ v1_funct_2(C_65,'#skF_2',B_64)
      | ~ v1_funct_1(C_65) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_196])).

tff(c_207,plain,
    ( k3_funct_2('#skF_2','#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3')) = k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3'))
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_204])).

tff(c_210,plain,(
    k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) = '#skF_1'('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_174,c_207])).

tff(c_212,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_169,c_210])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:48:06 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.27/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.34  
% 2.27/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.34  %$ r2_funct_2 > v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.27/1.34  
% 2.27/1.34  %Foreground sorts:
% 2.27/1.34  
% 2.27/1.34  
% 2.27/1.34  %Background operators:
% 2.27/1.34  
% 2.27/1.34  
% 2.27/1.34  %Foreground operators:
% 2.27/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.27/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.27/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.27/1.34  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.27/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.27/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.27/1.34  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.27/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.27/1.34  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.27/1.34  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.27/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.27/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.27/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.27/1.34  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.27/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.27/1.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.27/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.27/1.34  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.27/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.27/1.34  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 2.27/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.27/1.34  
% 2.27/1.36  tff(f_105, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => ((![C]: (m1_subset_1(C, A) => (k3_funct_2(A, A, B, C) = C))) => r2_funct_2(A, A, B, k6_partfun1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t201_funct_2)).
% 2.27/1.36  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.27/1.36  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.27/1.36  tff(f_87, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_2)).
% 2.27/1.36  tff(f_65, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.27/1.36  tff(f_42, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_funct_1)).
% 2.27/1.36  tff(f_79, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_funct_2(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_funct_2)).
% 2.27/1.36  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 2.27/1.36  tff(f_63, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.27/1.36  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.27/1.36  tff(c_49, plain, (![C_33, A_34, B_35]: (v1_relat_1(C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.27/1.36  tff(c_53, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_49])).
% 2.27/1.36  tff(c_32, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.27/1.36  tff(c_30, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.27/1.36  tff(c_56, plain, (![A_38, B_39, C_40]: (k1_relset_1(A_38, B_39, C_40)=k1_relat_1(C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.27/1.36  tff(c_60, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_56])).
% 2.27/1.36  tff(c_71, plain, (![A_44, B_45]: (k1_relset_1(A_44, A_44, B_45)=A_44 | ~m1_subset_1(B_45, k1_zfmisc_1(k2_zfmisc_1(A_44, A_44))) | ~v1_funct_2(B_45, A_44, A_44) | ~v1_funct_1(B_45))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.27/1.36  tff(c_74, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')='#skF_2' | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_71])).
% 2.27/1.36  tff(c_77, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_60, c_74])).
% 2.27/1.36  tff(c_18, plain, (![A_18]: (k6_relat_1(A_18)=k6_partfun1(A_18))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.27/1.36  tff(c_6, plain, (![B_4]: (r2_hidden('#skF_1'(k1_relat_1(B_4), B_4), k1_relat_1(B_4)) | k6_relat_1(k1_relat_1(B_4))=B_4 | ~v1_funct_1(B_4) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.27/1.36  tff(c_37, plain, (![B_4]: (r2_hidden('#skF_1'(k1_relat_1(B_4), B_4), k1_relat_1(B_4)) | k6_partfun1(k1_relat_1(B_4))=B_4 | ~v1_funct_1(B_4) | ~v1_relat_1(B_4))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_6])).
% 2.27/1.36  tff(c_85, plain, (r2_hidden('#skF_1'(k1_relat_1('#skF_3'), '#skF_3'), '#skF_2') | k6_partfun1(k1_relat_1('#skF_3'))='#skF_3' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_77, c_37])).
% 2.27/1.36  tff(c_91, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | k6_partfun1('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_53, c_32, c_77, c_77, c_85])).
% 2.27/1.36  tff(c_97, plain, (k6_partfun1('#skF_2')='#skF_3'), inference(splitLeft, [status(thm)], [c_91])).
% 2.27/1.36  tff(c_24, plain, (~r2_funct_2('#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.27/1.36  tff(c_99, plain, (~r2_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_24])).
% 2.27/1.36  tff(c_139, plain, (![A_53, B_54, C_55, D_56]: (r2_funct_2(A_53, B_54, C_55, C_55) | ~m1_subset_1(D_56, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))) | ~v1_funct_2(D_56, A_53, B_54) | ~v1_funct_1(D_56) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))) | ~v1_funct_2(C_55, A_53, B_54) | ~v1_funct_1(C_55))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.27/1.36  tff(c_141, plain, (![C_55]: (r2_funct_2('#skF_2', '#skF_2', C_55, C_55) | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2(C_55, '#skF_2', '#skF_2') | ~v1_funct_1(C_55))), inference(resolution, [status(thm)], [c_28, c_139])).
% 2.27/1.36  tff(c_145, plain, (![C_57]: (r2_funct_2('#skF_2', '#skF_2', C_57, C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2(C_57, '#skF_2', '#skF_2') | ~v1_funct_1(C_57))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_141])).
% 2.27/1.36  tff(c_147, plain, (r2_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_145])).
% 2.27/1.36  tff(c_150, plain, (r2_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_147])).
% 2.27/1.36  tff(c_152, plain, $false, inference(negUnitSimplification, [status(thm)], [c_99, c_150])).
% 2.27/1.36  tff(c_154, plain, (k6_partfun1('#skF_2')!='#skF_3'), inference(splitRight, [status(thm)], [c_91])).
% 2.27/1.36  tff(c_4, plain, (![B_4]: (k1_funct_1(B_4, '#skF_1'(k1_relat_1(B_4), B_4))!='#skF_1'(k1_relat_1(B_4), B_4) | k6_relat_1(k1_relat_1(B_4))=B_4 | ~v1_funct_1(B_4) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.27/1.36  tff(c_163, plain, (![B_58]: (k1_funct_1(B_58, '#skF_1'(k1_relat_1(B_58), B_58))!='#skF_1'(k1_relat_1(B_58), B_58) | k6_partfun1(k1_relat_1(B_58))=B_58 | ~v1_funct_1(B_58) | ~v1_relat_1(B_58))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_4])).
% 2.27/1.36  tff(c_166, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))!='#skF_1'(k1_relat_1('#skF_3'), '#skF_3') | k6_partfun1(k1_relat_1('#skF_3'))='#skF_3' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_77, c_163])).
% 2.27/1.36  tff(c_168, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))!='#skF_1'('#skF_2', '#skF_3') | k6_partfun1('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_53, c_32, c_77, c_77, c_166])).
% 2.27/1.36  tff(c_169, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))!='#skF_1'('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_154, c_168])).
% 2.27/1.36  tff(c_82, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), k1_relat_1('#skF_3')) | k6_partfun1(k1_relat_1('#skF_3'))='#skF_3' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_77, c_37])).
% 2.27/1.36  tff(c_89, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | k6_partfun1('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_53, c_32, c_77, c_77, c_82])).
% 2.27/1.36  tff(c_155, plain, (k6_partfun1('#skF_2')='#skF_3'), inference(splitLeft, [status(thm)], [c_89])).
% 2.27/1.36  tff(c_156, plain, $false, inference(negUnitSimplification, [status(thm)], [c_154, c_155])).
% 2.27/1.36  tff(c_157, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_89])).
% 2.27/1.36  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.27/1.36  tff(c_162, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_157, c_2])).
% 2.27/1.36  tff(c_26, plain, (![C_29]: (k3_funct_2('#skF_2', '#skF_2', '#skF_3', C_29)=C_29 | ~m1_subset_1(C_29, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.27/1.36  tff(c_174, plain, (k3_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3'))='#skF_1'('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_162, c_26])).
% 2.27/1.36  tff(c_34, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.27/1.36  tff(c_192, plain, (![A_60, B_61, C_62, D_63]: (k3_funct_2(A_60, B_61, C_62, D_63)=k1_funct_1(C_62, D_63) | ~m1_subset_1(D_63, A_60) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))) | ~v1_funct_2(C_62, A_60, B_61) | ~v1_funct_1(C_62) | v1_xboole_0(A_60))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.27/1.36  tff(c_196, plain, (![B_61, C_62]: (k3_funct_2('#skF_2', B_61, C_62, '#skF_1'('#skF_2', '#skF_3'))=k1_funct_1(C_62, '#skF_1'('#skF_2', '#skF_3')) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_61))) | ~v1_funct_2(C_62, '#skF_2', B_61) | ~v1_funct_1(C_62) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_162, c_192])).
% 2.27/1.36  tff(c_204, plain, (![B_64, C_65]: (k3_funct_2('#skF_2', B_64, C_65, '#skF_1'('#skF_2', '#skF_3'))=k1_funct_1(C_65, '#skF_1'('#skF_2', '#skF_3')) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_64))) | ~v1_funct_2(C_65, '#skF_2', B_64) | ~v1_funct_1(C_65))), inference(negUnitSimplification, [status(thm)], [c_34, c_196])).
% 2.27/1.36  tff(c_207, plain, (k3_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3'))=k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3')) | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_204])).
% 2.27/1.36  tff(c_210, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))='#skF_1'('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_174, c_207])).
% 2.27/1.36  tff(c_212, plain, $false, inference(negUnitSimplification, [status(thm)], [c_169, c_210])).
% 2.27/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.36  
% 2.27/1.36  Inference rules
% 2.27/1.36  ----------------------
% 2.27/1.36  #Ref     : 0
% 2.27/1.36  #Sup     : 36
% 2.27/1.36  #Fact    : 0
% 2.27/1.36  #Define  : 0
% 2.27/1.36  #Split   : 3
% 2.27/1.36  #Chain   : 0
% 2.27/1.36  #Close   : 0
% 2.27/1.36  
% 2.27/1.36  Ordering : KBO
% 2.27/1.36  
% 2.27/1.36  Simplification rules
% 2.27/1.36  ----------------------
% 2.27/1.36  #Subsume      : 1
% 2.27/1.36  #Demod        : 68
% 2.27/1.36  #Tautology    : 20
% 2.27/1.36  #SimpNegUnit  : 7
% 2.27/1.36  #BackRed      : 2
% 2.27/1.36  
% 2.27/1.36  #Partial instantiations: 0
% 2.27/1.36  #Strategies tried      : 1
% 2.27/1.36  
% 2.27/1.36  Timing (in seconds)
% 2.27/1.36  ----------------------
% 2.43/1.37  Preprocessing        : 0.34
% 2.43/1.37  Parsing              : 0.18
% 2.43/1.37  CNF conversion       : 0.02
% 2.43/1.37  Main loop            : 0.19
% 2.43/1.37  Inferencing          : 0.07
% 2.43/1.37  Reduction            : 0.06
% 2.43/1.37  Demodulation         : 0.05
% 2.43/1.37  BG Simplification    : 0.01
% 2.43/1.37  Subsumption          : 0.02
% 2.43/1.37  Abstraction          : 0.01
% 2.43/1.37  MUC search           : 0.00
% 2.43/1.37  Cooper               : 0.00
% 2.43/1.37  Total                : 0.56
% 2.43/1.37  Index Insertion      : 0.00
% 2.43/1.37  Index Deletion       : 0.00
% 2.43/1.37  Index Matching       : 0.00
% 2.43/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
