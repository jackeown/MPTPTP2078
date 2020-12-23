%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:22 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 460 expanded)
%              Number of leaves         :   34 ( 170 expanded)
%              Depth                    :   14
%              Number of atoms          :  166 (1216 expanded)
%              Number of equality atoms :   34 ( 197 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

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

tff(f_38,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_126,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t201_funct_2)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_94,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_108,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_funct_2(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_92,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(c_6,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_60,plain,(
    ! [B_41,A_42] :
      ( v1_relat_1(B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_42))
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_63,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_60])).

tff(c_66,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_63])).

tff(c_42,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_73,plain,(
    ! [C_47,A_48,B_49] :
      ( v4_relat_1(C_47,A_48)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_77,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_73])).

tff(c_80,plain,(
    ! [B_52,A_53] :
      ( k1_relat_1(B_52) = A_53
      | ~ v1_partfun1(B_52,A_53)
      | ~ v4_relat_1(B_52,A_53)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_83,plain,
    ( k1_relat_1('#skF_3') = '#skF_2'
    | ~ v1_partfun1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_77,c_80])).

tff(c_86,plain,
    ( k1_relat_1('#skF_3') = '#skF_2'
    | ~ v1_partfun1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_83])).

tff(c_87,plain,(
    ~ v1_partfun1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_40,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_95,plain,(
    ! [C_58,A_59,B_60] :
      ( v1_partfun1(C_58,A_59)
      | ~ v1_funct_2(C_58,A_59,B_60)
      | ~ v1_funct_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60)))
      | v1_xboole_0(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_98,plain,
    ( v1_partfun1('#skF_3','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_95])).

tff(c_101,plain,
    ( v1_partfun1('#skF_3','#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_98])).

tff(c_103,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_87,c_101])).

tff(c_104,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_30,plain,(
    ! [A_26] : k6_relat_1(A_26) = k6_partfun1(A_26) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_10,plain,(
    ! [B_9] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_9),B_9),k1_relat_1(B_9))
      | k6_relat_1(k1_relat_1(B_9)) = B_9
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_117,plain,(
    ! [B_63] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_63),B_63),k1_relat_1(B_63))
      | k6_partfun1(k1_relat_1(B_63)) = B_63
      | ~ v1_funct_1(B_63)
      | ~ v1_relat_1(B_63) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_10])).

tff(c_123,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),k1_relat_1('#skF_3'))
    | k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_117])).

tff(c_129,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | k6_partfun1('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_42,c_104,c_104,c_123])).

tff(c_132,plain,(
    k6_partfun1('#skF_2') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_129])).

tff(c_34,plain,(
    ~ r2_funct_2('#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_133,plain,(
    ~ r2_funct_2('#skF_2','#skF_2','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_34])).

tff(c_181,plain,(
    ! [A_74,B_75,C_76,D_77] :
      ( r2_funct_2(A_74,B_75,C_76,C_76)
      | ~ m1_subset_1(D_77,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75)))
      | ~ v1_funct_2(D_77,A_74,B_75)
      | ~ v1_funct_1(D_77)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75)))
      | ~ v1_funct_2(C_76,A_74,B_75)
      | ~ v1_funct_1(C_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_183,plain,(
    ! [C_76] :
      ( r2_funct_2('#skF_2','#skF_2',C_76,C_76)
      | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
      | ~ v1_funct_2(C_76,'#skF_2','#skF_2')
      | ~ v1_funct_1(C_76) ) ),
    inference(resolution,[status(thm)],[c_38,c_181])).

tff(c_188,plain,(
    ! [C_78] :
      ( r2_funct_2('#skF_2','#skF_2',C_78,C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
      | ~ v1_funct_2(C_78,'#skF_2','#skF_2')
      | ~ v1_funct_1(C_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_183])).

tff(c_190,plain,
    ( r2_funct_2('#skF_2','#skF_2','#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_188])).

tff(c_193,plain,(
    r2_funct_2('#skF_2','#skF_2','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_190])).

tff(c_195,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_193])).

tff(c_197,plain,(
    k6_partfun1('#skF_2') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_129])).

tff(c_8,plain,(
    ! [B_9] :
      ( k1_funct_1(B_9,'#skF_1'(k1_relat_1(B_9),B_9)) != '#skF_1'(k1_relat_1(B_9),B_9)
      | k6_relat_1(k1_relat_1(B_9)) = B_9
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_245,plain,(
    ! [B_87] :
      ( k1_funct_1(B_87,'#skF_1'(k1_relat_1(B_87),B_87)) != '#skF_1'(k1_relat_1(B_87),B_87)
      | k6_partfun1(k1_relat_1(B_87)) = B_87
      | ~ v1_funct_1(B_87)
      | ~ v1_relat_1(B_87) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_8])).

tff(c_248,plain,
    ( k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) != '#skF_1'(k1_relat_1('#skF_3'),'#skF_3')
    | k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_245])).

tff(c_250,plain,
    ( k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) != '#skF_1'('#skF_2','#skF_3')
    | k6_partfun1('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_42,c_104,c_104,c_248])).

tff(c_251,plain,(
    k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) != '#skF_1'('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_197,c_250])).

tff(c_196,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_129])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_201,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_196,c_2])).

tff(c_36,plain,(
    ! [C_35] :
      ( k3_funct_2('#skF_2','#skF_2','#skF_3',C_35) = C_35
      | ~ m1_subset_1(C_35,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_205,plain,(
    k3_funct_2('#skF_2','#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3')) = '#skF_1'('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_201,c_36])).

tff(c_233,plain,(
    ! [A_83,B_84,C_85,D_86] :
      ( k3_funct_2(A_83,B_84,C_85,D_86) = k1_funct_1(C_85,D_86)
      | ~ m1_subset_1(D_86,A_83)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84)))
      | ~ v1_funct_2(C_85,A_83,B_84)
      | ~ v1_funct_1(C_85)
      | v1_xboole_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_237,plain,(
    ! [B_84,C_85] :
      ( k3_funct_2('#skF_2',B_84,C_85,'#skF_1'('#skF_2','#skF_3')) = k1_funct_1(C_85,'#skF_1'('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_84)))
      | ~ v1_funct_2(C_85,'#skF_2',B_84)
      | ~ v1_funct_1(C_85)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_201,c_233])).

tff(c_252,plain,(
    ! [B_88,C_89] :
      ( k3_funct_2('#skF_2',B_88,C_89,'#skF_1'('#skF_2','#skF_3')) = k1_funct_1(C_89,'#skF_1'('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_88)))
      | ~ v1_funct_2(C_89,'#skF_2',B_88)
      | ~ v1_funct_1(C_89) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_237])).

tff(c_255,plain,
    ( k3_funct_2('#skF_2','#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3')) = k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3'))
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_252])).

tff(c_258,plain,(
    k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) = '#skF_1'('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_205,c_255])).

tff(c_260,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_251,c_258])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:23:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.38/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.35  
% 2.38/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.35  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.38/1.35  
% 2.38/1.35  %Foreground sorts:
% 2.38/1.35  
% 2.38/1.35  
% 2.38/1.35  %Background operators:
% 2.38/1.35  
% 2.38/1.35  
% 2.38/1.35  %Foreground operators:
% 2.38/1.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.38/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.38/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.38/1.35  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.38/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.38/1.35  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.38/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.38/1.35  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.38/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.38/1.35  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.38/1.35  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.38/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.38/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.38/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.38/1.35  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.38/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.38/1.35  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.38/1.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.38/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.38/1.35  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.38/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.38/1.35  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 2.38/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.38/1.35  
% 2.54/1.37  tff(f_38, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.54/1.37  tff(f_126, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => ((![C]: (m1_subset_1(C, A) => (k3_funct_2(A, A, B, C) = C))) => r2_funct_2(A, A, B, k6_partfun1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t201_funct_2)).
% 2.54/1.37  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.54/1.37  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.54/1.37  tff(f_79, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 2.54/1.37  tff(f_71, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.54/1.37  tff(f_94, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.54/1.37  tff(f_51, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_funct_1)).
% 2.54/1.37  tff(f_108, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_funct_2(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_funct_2)).
% 2.54/1.37  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 2.54/1.37  tff(f_92, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.54/1.37  tff(c_6, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.54/1.37  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.54/1.37  tff(c_60, plain, (![B_41, A_42]: (v1_relat_1(B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(A_42)) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.54/1.37  tff(c_63, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_60])).
% 2.54/1.37  tff(c_66, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_63])).
% 2.54/1.37  tff(c_42, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.54/1.37  tff(c_44, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.54/1.37  tff(c_73, plain, (![C_47, A_48, B_49]: (v4_relat_1(C_47, A_48) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.54/1.37  tff(c_77, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_73])).
% 2.54/1.37  tff(c_80, plain, (![B_52, A_53]: (k1_relat_1(B_52)=A_53 | ~v1_partfun1(B_52, A_53) | ~v4_relat_1(B_52, A_53) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.54/1.37  tff(c_83, plain, (k1_relat_1('#skF_3')='#skF_2' | ~v1_partfun1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_77, c_80])).
% 2.54/1.37  tff(c_86, plain, (k1_relat_1('#skF_3')='#skF_2' | ~v1_partfun1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_83])).
% 2.54/1.37  tff(c_87, plain, (~v1_partfun1('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_86])).
% 2.54/1.37  tff(c_40, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.54/1.37  tff(c_95, plain, (![C_58, A_59, B_60]: (v1_partfun1(C_58, A_59) | ~v1_funct_2(C_58, A_59, B_60) | ~v1_funct_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))) | v1_xboole_0(B_60))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.54/1.37  tff(c_98, plain, (v1_partfun1('#skF_3', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_95])).
% 2.54/1.37  tff(c_101, plain, (v1_partfun1('#skF_3', '#skF_2') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_98])).
% 2.54/1.37  tff(c_103, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_87, c_101])).
% 2.54/1.37  tff(c_104, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_86])).
% 2.54/1.37  tff(c_30, plain, (![A_26]: (k6_relat_1(A_26)=k6_partfun1(A_26))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.54/1.37  tff(c_10, plain, (![B_9]: (r2_hidden('#skF_1'(k1_relat_1(B_9), B_9), k1_relat_1(B_9)) | k6_relat_1(k1_relat_1(B_9))=B_9 | ~v1_funct_1(B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.54/1.37  tff(c_117, plain, (![B_63]: (r2_hidden('#skF_1'(k1_relat_1(B_63), B_63), k1_relat_1(B_63)) | k6_partfun1(k1_relat_1(B_63))=B_63 | ~v1_funct_1(B_63) | ~v1_relat_1(B_63))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_10])).
% 2.54/1.37  tff(c_123, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), k1_relat_1('#skF_3')) | k6_partfun1(k1_relat_1('#skF_3'))='#skF_3' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_104, c_117])).
% 2.54/1.37  tff(c_129, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | k6_partfun1('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_42, c_104, c_104, c_123])).
% 2.54/1.37  tff(c_132, plain, (k6_partfun1('#skF_2')='#skF_3'), inference(splitLeft, [status(thm)], [c_129])).
% 2.54/1.37  tff(c_34, plain, (~r2_funct_2('#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.54/1.37  tff(c_133, plain, (~r2_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_34])).
% 2.54/1.37  tff(c_181, plain, (![A_74, B_75, C_76, D_77]: (r2_funct_2(A_74, B_75, C_76, C_76) | ~m1_subset_1(D_77, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))) | ~v1_funct_2(D_77, A_74, B_75) | ~v1_funct_1(D_77) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))) | ~v1_funct_2(C_76, A_74, B_75) | ~v1_funct_1(C_76))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.54/1.37  tff(c_183, plain, (![C_76]: (r2_funct_2('#skF_2', '#skF_2', C_76, C_76) | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2(C_76, '#skF_2', '#skF_2') | ~v1_funct_1(C_76))), inference(resolution, [status(thm)], [c_38, c_181])).
% 2.54/1.37  tff(c_188, plain, (![C_78]: (r2_funct_2('#skF_2', '#skF_2', C_78, C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2(C_78, '#skF_2', '#skF_2') | ~v1_funct_1(C_78))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_183])).
% 2.54/1.37  tff(c_190, plain, (r2_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_188])).
% 2.54/1.37  tff(c_193, plain, (r2_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_190])).
% 2.54/1.37  tff(c_195, plain, $false, inference(negUnitSimplification, [status(thm)], [c_133, c_193])).
% 2.54/1.37  tff(c_197, plain, (k6_partfun1('#skF_2')!='#skF_3'), inference(splitRight, [status(thm)], [c_129])).
% 2.54/1.37  tff(c_8, plain, (![B_9]: (k1_funct_1(B_9, '#skF_1'(k1_relat_1(B_9), B_9))!='#skF_1'(k1_relat_1(B_9), B_9) | k6_relat_1(k1_relat_1(B_9))=B_9 | ~v1_funct_1(B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.54/1.37  tff(c_245, plain, (![B_87]: (k1_funct_1(B_87, '#skF_1'(k1_relat_1(B_87), B_87))!='#skF_1'(k1_relat_1(B_87), B_87) | k6_partfun1(k1_relat_1(B_87))=B_87 | ~v1_funct_1(B_87) | ~v1_relat_1(B_87))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_8])).
% 2.54/1.37  tff(c_248, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))!='#skF_1'(k1_relat_1('#skF_3'), '#skF_3') | k6_partfun1(k1_relat_1('#skF_3'))='#skF_3' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_104, c_245])).
% 2.54/1.37  tff(c_250, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))!='#skF_1'('#skF_2', '#skF_3') | k6_partfun1('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_42, c_104, c_104, c_248])).
% 2.54/1.37  tff(c_251, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))!='#skF_1'('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_197, c_250])).
% 2.54/1.37  tff(c_196, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_129])).
% 2.54/1.37  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.54/1.37  tff(c_201, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_196, c_2])).
% 2.54/1.37  tff(c_36, plain, (![C_35]: (k3_funct_2('#skF_2', '#skF_2', '#skF_3', C_35)=C_35 | ~m1_subset_1(C_35, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.54/1.37  tff(c_205, plain, (k3_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3'))='#skF_1'('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_201, c_36])).
% 2.54/1.37  tff(c_233, plain, (![A_83, B_84, C_85, D_86]: (k3_funct_2(A_83, B_84, C_85, D_86)=k1_funct_1(C_85, D_86) | ~m1_subset_1(D_86, A_83) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))) | ~v1_funct_2(C_85, A_83, B_84) | ~v1_funct_1(C_85) | v1_xboole_0(A_83))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.54/1.37  tff(c_237, plain, (![B_84, C_85]: (k3_funct_2('#skF_2', B_84, C_85, '#skF_1'('#skF_2', '#skF_3'))=k1_funct_1(C_85, '#skF_1'('#skF_2', '#skF_3')) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_84))) | ~v1_funct_2(C_85, '#skF_2', B_84) | ~v1_funct_1(C_85) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_201, c_233])).
% 2.54/1.37  tff(c_252, plain, (![B_88, C_89]: (k3_funct_2('#skF_2', B_88, C_89, '#skF_1'('#skF_2', '#skF_3'))=k1_funct_1(C_89, '#skF_1'('#skF_2', '#skF_3')) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_88))) | ~v1_funct_2(C_89, '#skF_2', B_88) | ~v1_funct_1(C_89))), inference(negUnitSimplification, [status(thm)], [c_44, c_237])).
% 2.54/1.37  tff(c_255, plain, (k3_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3'))=k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3')) | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_252])).
% 2.54/1.37  tff(c_258, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))='#skF_1'('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_205, c_255])).
% 2.54/1.37  tff(c_260, plain, $false, inference(negUnitSimplification, [status(thm)], [c_251, c_258])).
% 2.54/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.37  
% 2.54/1.37  Inference rules
% 2.54/1.37  ----------------------
% 2.54/1.37  #Ref     : 0
% 2.54/1.37  #Sup     : 38
% 2.54/1.37  #Fact    : 0
% 2.54/1.37  #Define  : 0
% 2.54/1.37  #Split   : 3
% 2.54/1.37  #Chain   : 0
% 2.54/1.37  #Close   : 0
% 2.54/1.37  
% 2.54/1.37  Ordering : KBO
% 2.54/1.37  
% 2.54/1.37  Simplification rules
% 2.54/1.37  ----------------------
% 2.54/1.37  #Subsume      : 0
% 2.54/1.37  #Demod        : 78
% 2.54/1.37  #Tautology    : 20
% 2.54/1.37  #SimpNegUnit  : 10
% 2.54/1.37  #BackRed      : 1
% 2.54/1.37  
% 2.54/1.37  #Partial instantiations: 0
% 2.54/1.37  #Strategies tried      : 1
% 2.54/1.37  
% 2.54/1.37  Timing (in seconds)
% 2.54/1.37  ----------------------
% 2.54/1.37  Preprocessing        : 0.37
% 2.54/1.37  Parsing              : 0.20
% 2.54/1.37  CNF conversion       : 0.02
% 2.54/1.37  Main loop            : 0.21
% 2.54/1.37  Inferencing          : 0.08
% 2.54/1.37  Reduction            : 0.07
% 2.54/1.37  Demodulation         : 0.05
% 2.54/1.37  BG Simplification    : 0.02
% 2.54/1.37  Subsumption          : 0.03
% 2.54/1.37  Abstraction          : 0.01
% 2.54/1.37  MUC search           : 0.00
% 2.54/1.37  Cooper               : 0.00
% 2.54/1.37  Total                : 0.62
% 2.54/1.37  Index Insertion      : 0.00
% 2.54/1.37  Index Deletion       : 0.00
% 2.54/1.37  Index Matching       : 0.00
% 2.54/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
