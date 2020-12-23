%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:52 EST 2020

% Result     : Theorem 3.66s
% Output     : CNFRefutation 3.66s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 258 expanded)
%              Number of leaves         :   30 ( 104 expanded)
%              Depth                    :   10
%              Number of atoms          :  200 ( 788 expanded)
%              Number of equality atoms :   18 (  88 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_107,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_44,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_56,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(c_42,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_938,plain,(
    ! [A_178,B_179,C_180] :
      ( k1_relset_1(A_178,B_179,C_180) = k1_relat_1(C_180)
      | ~ m1_subset_1(C_180,k1_zfmisc_1(k2_zfmisc_1(A_178,B_179))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_951,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_938])).

tff(c_1036,plain,(
    ! [A_192,B_193,C_194] :
      ( m1_subset_1(k1_relset_1(A_192,B_193,C_194),k1_zfmisc_1(A_192))
      | ~ m1_subset_1(C_194,k1_zfmisc_1(k2_zfmisc_1(A_192,B_193))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1056,plain,
    ( m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_951,c_1036])).

tff(c_1064,plain,(
    m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1056])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1072,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_1064,c_2])).

tff(c_12,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_97,plain,(
    ! [B_37,A_38] :
      ( v1_relat_1(B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_38))
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_103,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_42,c_97])).

tff(c_107,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_103])).

tff(c_46,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_40,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_20,plain,(
    ! [A_11] :
      ( k2_relat_1(k2_funct_1(A_11)) = k1_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_158,plain,(
    ! [A_52,B_53,C_54] :
      ( k1_relset_1(A_52,B_53,C_54) = k1_relat_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_167,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_158])).

tff(c_234,plain,(
    ! [A_68,B_69,C_70] :
      ( m1_subset_1(k1_relset_1(A_68,B_69,C_70),k1_zfmisc_1(A_68))
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_251,plain,
    ( m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_234])).

tff(c_257,plain,(
    m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_251])).

tff(c_265,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_257,c_2])).

tff(c_18,plain,(
    ! [A_10] :
      ( v1_relat_1(k2_funct_1(A_10))
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_63,plain,(
    ! [B_29,A_30] :
      ( v1_relat_1(B_29)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_30))
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_69,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_42,c_63])).

tff(c_73,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_69])).

tff(c_87,plain,(
    ! [A_36] :
      ( v1_funct_1(k2_funct_1(A_36))
      | ~ v2_funct_1(A_36)
      | ~ v1_funct_1(A_36)
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_36,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_62,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_90,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_87,c_62])).

tff(c_94,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_46,c_40,c_90])).

tff(c_96,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_38,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_183,plain,(
    ! [A_58,B_59,C_60] :
      ( k2_relset_1(A_58,B_59,C_60) = k2_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_190,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_183])).

tff(c_193,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_190])).

tff(c_22,plain,(
    ! [A_11] :
      ( k1_relat_1(k2_funct_1(A_11)) = k2_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_219,plain,(
    ! [B_63,A_64] :
      ( v1_funct_2(B_63,k1_relat_1(B_63),A_64)
      | ~ r1_tarski(k2_relat_1(B_63),A_64)
      | ~ v1_funct_1(B_63)
      | ~ v1_relat_1(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_571,plain,(
    ! [A_117,A_118] :
      ( v1_funct_2(k2_funct_1(A_117),k2_relat_1(A_117),A_118)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_117)),A_118)
      | ~ v1_funct_1(k2_funct_1(A_117))
      | ~ v1_relat_1(k2_funct_1(A_117))
      | ~ v2_funct_1(A_117)
      | ~ v1_funct_1(A_117)
      | ~ v1_relat_1(A_117) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_219])).

tff(c_574,plain,(
    ! [A_118] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_118)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_118)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_571])).

tff(c_579,plain,(
    ! [A_118] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_118)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_118)
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_46,c_40,c_96,c_574])).

tff(c_580,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_579])).

tff(c_583,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_580])).

tff(c_587,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_46,c_40,c_583])).

tff(c_589,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_579])).

tff(c_271,plain,(
    ! [B_71,A_72] :
      ( m1_subset_1(B_71,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_71),A_72)))
      | ~ r1_tarski(k2_relat_1(B_71),A_72)
      | ~ v1_funct_1(B_71)
      | ~ v1_relat_1(B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_802,plain,(
    ! [A_162,A_163] :
      ( m1_subset_1(k2_funct_1(A_162),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_162),A_163)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_162)),A_163)
      | ~ v1_funct_1(k2_funct_1(A_162))
      | ~ v1_relat_1(k2_funct_1(A_162))
      | ~ v2_funct_1(A_162)
      | ~ v1_funct_1(A_162)
      | ~ v1_relat_1(A_162) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_271])).

tff(c_822,plain,(
    ! [A_163] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_163)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_163)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_802])).

tff(c_836,plain,(
    ! [A_164] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_164)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_164) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_46,c_40,c_589,c_96,c_822])).

tff(c_95,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_108,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_95])).

tff(c_861,plain,(
    ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_836,c_108])).

tff(c_868,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_861])).

tff(c_874,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_46,c_40,c_265,c_868])).

tff(c_876,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_95])).

tff(c_6,plain,(
    ! [B_5,A_3] :
      ( v1_relat_1(B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_3))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_879,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_876,c_6])).

tff(c_885,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_879])).

tff(c_960,plain,(
    ! [A_181,B_182,C_183] :
      ( k2_relset_1(A_181,B_182,C_183) = k2_relat_1(C_183)
      | ~ m1_subset_1(C_183,k1_zfmisc_1(k2_zfmisc_1(A_181,B_182))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_970,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_960])).

tff(c_974,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_970])).

tff(c_1077,plain,(
    ! [B_195,A_196] :
      ( v1_funct_2(B_195,k1_relat_1(B_195),A_196)
      | ~ r1_tarski(k2_relat_1(B_195),A_196)
      | ~ v1_funct_1(B_195)
      | ~ v1_relat_1(B_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1568,plain,(
    ! [A_256,A_257] :
      ( v1_funct_2(k2_funct_1(A_256),k2_relat_1(A_256),A_257)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_256)),A_257)
      | ~ v1_funct_1(k2_funct_1(A_256))
      | ~ v1_relat_1(k2_funct_1(A_256))
      | ~ v2_funct_1(A_256)
      | ~ v1_funct_1(A_256)
      | ~ v1_relat_1(A_256) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1077])).

tff(c_1571,plain,(
    ! [A_257] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_257)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_257)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_974,c_1568])).

tff(c_1577,plain,(
    ! [A_258] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_258)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_258) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_46,c_40,c_885,c_96,c_1571])).

tff(c_1584,plain,(
    ! [A_258] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_258)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_258)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1577])).

tff(c_1595,plain,(
    ! [A_259] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_259)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_259) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_46,c_40,c_1584])).

tff(c_875,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_95])).

tff(c_1598,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_1595,c_875])).

tff(c_1602,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1072,c_1598])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:20:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.66/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.66/1.62  
% 3.66/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.66/1.62  %$ v1_funct_2 > v5_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.66/1.62  
% 3.66/1.62  %Foreground sorts:
% 3.66/1.62  
% 3.66/1.62  
% 3.66/1.62  %Background operators:
% 3.66/1.62  
% 3.66/1.62  
% 3.66/1.62  %Foreground operators:
% 3.66/1.62  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.66/1.62  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.66/1.62  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.66/1.62  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.66/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.66/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.66/1.62  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.66/1.62  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.66/1.62  tff('#skF_2', type, '#skF_2': $i).
% 3.66/1.62  tff('#skF_3', type, '#skF_3': $i).
% 3.66/1.62  tff('#skF_1', type, '#skF_1': $i).
% 3.66/1.62  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.66/1.62  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.66/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.66/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.66/1.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.66/1.62  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.66/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.66/1.62  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.66/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.66/1.62  
% 3.66/1.64  tff(f_107, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 3.66/1.64  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.66/1.64  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 3.66/1.64  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.66/1.64  tff(f_44, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.66/1.64  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.66/1.64  tff(f_66, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 3.66/1.64  tff(f_56, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_funct_1)).
% 3.66/1.64  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.66/1.64  tff(f_90, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 3.66/1.64  tff(c_42, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.66/1.64  tff(c_938, plain, (![A_178, B_179, C_180]: (k1_relset_1(A_178, B_179, C_180)=k1_relat_1(C_180) | ~m1_subset_1(C_180, k1_zfmisc_1(k2_zfmisc_1(A_178, B_179))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.66/1.64  tff(c_951, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_938])).
% 3.66/1.64  tff(c_1036, plain, (![A_192, B_193, C_194]: (m1_subset_1(k1_relset_1(A_192, B_193, C_194), k1_zfmisc_1(A_192)) | ~m1_subset_1(C_194, k1_zfmisc_1(k2_zfmisc_1(A_192, B_193))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.66/1.64  tff(c_1056, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_951, c_1036])).
% 3.66/1.64  tff(c_1064, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1056])).
% 3.66/1.64  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.66/1.64  tff(c_1072, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_1064, c_2])).
% 3.66/1.64  tff(c_12, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.66/1.64  tff(c_97, plain, (![B_37, A_38]: (v1_relat_1(B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(A_38)) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.66/1.64  tff(c_103, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_42, c_97])).
% 3.66/1.64  tff(c_107, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_103])).
% 3.66/1.64  tff(c_46, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.66/1.64  tff(c_40, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.66/1.64  tff(c_20, plain, (![A_11]: (k2_relat_1(k2_funct_1(A_11))=k1_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.66/1.64  tff(c_158, plain, (![A_52, B_53, C_54]: (k1_relset_1(A_52, B_53, C_54)=k1_relat_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.66/1.64  tff(c_167, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_158])).
% 3.66/1.64  tff(c_234, plain, (![A_68, B_69, C_70]: (m1_subset_1(k1_relset_1(A_68, B_69, C_70), k1_zfmisc_1(A_68)) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.66/1.64  tff(c_251, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_167, c_234])).
% 3.66/1.64  tff(c_257, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_251])).
% 3.66/1.64  tff(c_265, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_257, c_2])).
% 3.66/1.64  tff(c_18, plain, (![A_10]: (v1_relat_1(k2_funct_1(A_10)) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.66/1.64  tff(c_63, plain, (![B_29, A_30]: (v1_relat_1(B_29) | ~m1_subset_1(B_29, k1_zfmisc_1(A_30)) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.66/1.64  tff(c_69, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_42, c_63])).
% 3.66/1.64  tff(c_73, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_69])).
% 3.66/1.64  tff(c_87, plain, (![A_36]: (v1_funct_1(k2_funct_1(A_36)) | ~v2_funct_1(A_36) | ~v1_funct_1(A_36) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.66/1.64  tff(c_36, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.66/1.64  tff(c_62, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_36])).
% 3.66/1.64  tff(c_90, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_87, c_62])).
% 3.66/1.64  tff(c_94, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73, c_46, c_40, c_90])).
% 3.66/1.64  tff(c_96, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_36])).
% 3.66/1.64  tff(c_38, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.66/1.64  tff(c_183, plain, (![A_58, B_59, C_60]: (k2_relset_1(A_58, B_59, C_60)=k2_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.66/1.64  tff(c_190, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_183])).
% 3.66/1.64  tff(c_193, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_190])).
% 3.66/1.64  tff(c_22, plain, (![A_11]: (k1_relat_1(k2_funct_1(A_11))=k2_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.66/1.64  tff(c_219, plain, (![B_63, A_64]: (v1_funct_2(B_63, k1_relat_1(B_63), A_64) | ~r1_tarski(k2_relat_1(B_63), A_64) | ~v1_funct_1(B_63) | ~v1_relat_1(B_63))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.66/1.64  tff(c_571, plain, (![A_117, A_118]: (v1_funct_2(k2_funct_1(A_117), k2_relat_1(A_117), A_118) | ~r1_tarski(k2_relat_1(k2_funct_1(A_117)), A_118) | ~v1_funct_1(k2_funct_1(A_117)) | ~v1_relat_1(k2_funct_1(A_117)) | ~v2_funct_1(A_117) | ~v1_funct_1(A_117) | ~v1_relat_1(A_117))), inference(superposition, [status(thm), theory('equality')], [c_22, c_219])).
% 3.66/1.64  tff(c_574, plain, (![A_118]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_118) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_118) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_193, c_571])).
% 3.66/1.64  tff(c_579, plain, (![A_118]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_118) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_118) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_46, c_40, c_96, c_574])).
% 3.66/1.64  tff(c_580, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_579])).
% 3.66/1.64  tff(c_583, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_580])).
% 3.66/1.64  tff(c_587, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_107, c_46, c_40, c_583])).
% 3.66/1.64  tff(c_589, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_579])).
% 3.66/1.64  tff(c_271, plain, (![B_71, A_72]: (m1_subset_1(B_71, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_71), A_72))) | ~r1_tarski(k2_relat_1(B_71), A_72) | ~v1_funct_1(B_71) | ~v1_relat_1(B_71))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.66/1.64  tff(c_802, plain, (![A_162, A_163]: (m1_subset_1(k2_funct_1(A_162), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_162), A_163))) | ~r1_tarski(k2_relat_1(k2_funct_1(A_162)), A_163) | ~v1_funct_1(k2_funct_1(A_162)) | ~v1_relat_1(k2_funct_1(A_162)) | ~v2_funct_1(A_162) | ~v1_funct_1(A_162) | ~v1_relat_1(A_162))), inference(superposition, [status(thm), theory('equality')], [c_22, c_271])).
% 3.66/1.64  tff(c_822, plain, (![A_163]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_163))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_163) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_193, c_802])).
% 3.66/1.64  tff(c_836, plain, (![A_164]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_164))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_164))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_46, c_40, c_589, c_96, c_822])).
% 3.66/1.64  tff(c_95, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_36])).
% 3.66/1.64  tff(c_108, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_95])).
% 3.66/1.64  tff(c_861, plain, (~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1')), inference(resolution, [status(thm)], [c_836, c_108])).
% 3.66/1.64  tff(c_868, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_20, c_861])).
% 3.66/1.64  tff(c_874, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_107, c_46, c_40, c_265, c_868])).
% 3.66/1.64  tff(c_876, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_95])).
% 3.66/1.64  tff(c_6, plain, (![B_5, A_3]: (v1_relat_1(B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_3)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.66/1.64  tff(c_879, plain, (v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_876, c_6])).
% 3.66/1.64  tff(c_885, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_879])).
% 3.66/1.64  tff(c_960, plain, (![A_181, B_182, C_183]: (k2_relset_1(A_181, B_182, C_183)=k2_relat_1(C_183) | ~m1_subset_1(C_183, k1_zfmisc_1(k2_zfmisc_1(A_181, B_182))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.66/1.64  tff(c_970, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_960])).
% 3.66/1.64  tff(c_974, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_970])).
% 3.66/1.64  tff(c_1077, plain, (![B_195, A_196]: (v1_funct_2(B_195, k1_relat_1(B_195), A_196) | ~r1_tarski(k2_relat_1(B_195), A_196) | ~v1_funct_1(B_195) | ~v1_relat_1(B_195))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.66/1.64  tff(c_1568, plain, (![A_256, A_257]: (v1_funct_2(k2_funct_1(A_256), k2_relat_1(A_256), A_257) | ~r1_tarski(k2_relat_1(k2_funct_1(A_256)), A_257) | ~v1_funct_1(k2_funct_1(A_256)) | ~v1_relat_1(k2_funct_1(A_256)) | ~v2_funct_1(A_256) | ~v1_funct_1(A_256) | ~v1_relat_1(A_256))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1077])).
% 3.66/1.64  tff(c_1571, plain, (![A_257]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_257) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_257) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_974, c_1568])).
% 3.66/1.64  tff(c_1577, plain, (![A_258]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_258) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_258))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_46, c_40, c_885, c_96, c_1571])).
% 3.66/1.64  tff(c_1584, plain, (![A_258]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_258) | ~r1_tarski(k1_relat_1('#skF_3'), A_258) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1577])).
% 3.66/1.64  tff(c_1595, plain, (![A_259]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_259) | ~r1_tarski(k1_relat_1('#skF_3'), A_259))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_46, c_40, c_1584])).
% 3.66/1.64  tff(c_875, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_95])).
% 3.66/1.64  tff(c_1598, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_1595, c_875])).
% 3.66/1.64  tff(c_1602, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1072, c_1598])).
% 3.66/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.66/1.64  
% 3.66/1.64  Inference rules
% 3.66/1.64  ----------------------
% 3.66/1.64  #Ref     : 0
% 3.66/1.64  #Sup     : 340
% 3.66/1.64  #Fact    : 0
% 3.66/1.64  #Define  : 0
% 3.66/1.64  #Split   : 12
% 3.66/1.64  #Chain   : 0
% 3.66/1.64  #Close   : 0
% 3.66/1.64  
% 3.66/1.64  Ordering : KBO
% 3.66/1.64  
% 3.66/1.64  Simplification rules
% 3.66/1.64  ----------------------
% 3.66/1.64  #Subsume      : 61
% 3.66/1.64  #Demod        : 200
% 3.66/1.64  #Tautology    : 90
% 3.66/1.64  #SimpNegUnit  : 7
% 3.66/1.64  #BackRed      : 5
% 3.66/1.64  
% 3.66/1.64  #Partial instantiations: 0
% 3.66/1.64  #Strategies tried      : 1
% 3.66/1.64  
% 3.66/1.64  Timing (in seconds)
% 3.66/1.64  ----------------------
% 3.66/1.64  Preprocessing        : 0.31
% 3.66/1.64  Parsing              : 0.17
% 3.66/1.64  CNF conversion       : 0.02
% 3.66/1.64  Main loop            : 0.56
% 3.66/1.64  Inferencing          : 0.22
% 3.66/1.64  Reduction            : 0.16
% 3.66/1.64  Demodulation         : 0.11
% 3.66/1.64  BG Simplification    : 0.03
% 3.66/1.64  Subsumption          : 0.10
% 3.66/1.65  Abstraction          : 0.03
% 3.66/1.65  MUC search           : 0.00
% 3.66/1.65  Cooper               : 0.00
% 3.66/1.65  Total                : 0.91
% 3.66/1.65  Index Insertion      : 0.00
% 3.66/1.65  Index Deletion       : 0.00
% 3.66/1.65  Index Matching       : 0.00
% 3.66/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
