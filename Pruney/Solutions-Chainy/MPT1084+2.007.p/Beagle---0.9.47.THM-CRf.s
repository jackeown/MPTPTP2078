%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:20 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 397 expanded)
%              Number of leaves         :   33 ( 149 expanded)
%              Depth                    :   14
%              Number of atoms          :  160 (1090 expanded)
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

tff(f_121,negated_conjecture,(
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

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_89,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_103,axiom,(
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

tff(f_87,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_57,plain,(
    ! [C_37,A_38,B_39] :
      ( v1_relat_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_61,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_57])).

tff(c_40,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_42,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_68,plain,(
    ! [C_44,A_45,B_46] :
      ( v4_relat_1(C_44,A_45)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_72,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_68])).

tff(c_75,plain,(
    ! [B_49,A_50] :
      ( k1_relat_1(B_49) = A_50
      | ~ v1_partfun1(B_49,A_50)
      | ~ v4_relat_1(B_49,A_50)
      | ~ v1_relat_1(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_78,plain,
    ( k1_relat_1('#skF_3') = '#skF_2'
    | ~ v1_partfun1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_75])).

tff(c_81,plain,
    ( k1_relat_1('#skF_3') = '#skF_2'
    | ~ v1_partfun1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_78])).

tff(c_82,plain,(
    ~ v1_partfun1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_81])).

tff(c_38,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_83,plain,(
    ! [C_51,A_52,B_53] :
      ( v1_partfun1(C_51,A_52)
      | ~ v1_funct_2(C_51,A_52,B_53)
      | ~ v1_funct_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53)))
      | v1_xboole_0(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_86,plain,
    ( v1_partfun1('#skF_3','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_83])).

tff(c_89,plain,
    ( v1_partfun1('#skF_3','#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_86])).

tff(c_91,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_82,c_89])).

tff(c_92,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_28,plain,(
    ! [A_24] : k6_relat_1(A_24) = k6_partfun1(A_24) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_6,plain,(
    ! [B_4] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_4),B_4),k1_relat_1(B_4))
      | k6_relat_1(k1_relat_1(B_4)) = B_4
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_105,plain,(
    ! [B_56] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_56),B_56),k1_relat_1(B_56))
      | k6_partfun1(k1_relat_1(B_56)) = B_56
      | ~ v1_funct_1(B_56)
      | ~ v1_relat_1(B_56) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_6])).

tff(c_111,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),k1_relat_1('#skF_3'))
    | k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_105])).

tff(c_117,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | k6_partfun1('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_40,c_92,c_92,c_111])).

tff(c_128,plain,(
    k6_partfun1('#skF_2') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_117])).

tff(c_32,plain,(
    ~ r2_funct_2('#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_129,plain,(
    ~ r2_funct_2('#skF_2','#skF_2','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_32])).

tff(c_169,plain,(
    ! [A_67,B_68,C_69,D_70] :
      ( r2_funct_2(A_67,B_68,C_69,C_69)
      | ~ m1_subset_1(D_70,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68)))
      | ~ v1_funct_2(D_70,A_67,B_68)
      | ~ v1_funct_1(D_70)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68)))
      | ~ v1_funct_2(C_69,A_67,B_68)
      | ~ v1_funct_1(C_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_171,plain,(
    ! [C_69] :
      ( r2_funct_2('#skF_2','#skF_2',C_69,C_69)
      | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
      | ~ v1_funct_2(C_69,'#skF_2','#skF_2')
      | ~ v1_funct_1(C_69) ) ),
    inference(resolution,[status(thm)],[c_36,c_169])).

tff(c_175,plain,(
    ! [C_71] :
      ( r2_funct_2('#skF_2','#skF_2',C_71,C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
      | ~ v1_funct_2(C_71,'#skF_2','#skF_2')
      | ~ v1_funct_1(C_71) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_171])).

tff(c_177,plain,
    ( r2_funct_2('#skF_2','#skF_2','#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_175])).

tff(c_180,plain,(
    r2_funct_2('#skF_2','#skF_2','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_177])).

tff(c_182,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_180])).

tff(c_184,plain,(
    k6_partfun1('#skF_2') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_117])).

tff(c_4,plain,(
    ! [B_4] :
      ( k1_funct_1(B_4,'#skF_1'(k1_relat_1(B_4),B_4)) != '#skF_1'(k1_relat_1(B_4),B_4)
      | k6_relat_1(k1_relat_1(B_4)) = B_4
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_212,plain,(
    ! [B_73] :
      ( k1_funct_1(B_73,'#skF_1'(k1_relat_1(B_73),B_73)) != '#skF_1'(k1_relat_1(B_73),B_73)
      | k6_partfun1(k1_relat_1(B_73)) = B_73
      | ~ v1_funct_1(B_73)
      | ~ v1_relat_1(B_73) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_4])).

tff(c_215,plain,
    ( k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) != '#skF_1'(k1_relat_1('#skF_3'),'#skF_3')
    | k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_212])).

tff(c_217,plain,
    ( k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) != '#skF_1'('#skF_2','#skF_3')
    | k6_partfun1('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_40,c_92,c_92,c_215])).

tff(c_218,plain,(
    k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) != '#skF_1'('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_184,c_217])).

tff(c_183,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_117])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_188,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_183,c_2])).

tff(c_34,plain,(
    ! [C_33] :
      ( k3_funct_2('#skF_2','#skF_2','#skF_3',C_33) = C_33
      | ~ m1_subset_1(C_33,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_192,plain,(
    k3_funct_2('#skF_2','#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3')) = '#skF_1'('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_188,c_34])).

tff(c_219,plain,(
    ! [A_74,B_75,C_76,D_77] :
      ( k3_funct_2(A_74,B_75,C_76,D_77) = k1_funct_1(C_76,D_77)
      | ~ m1_subset_1(D_77,A_74)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75)))
      | ~ v1_funct_2(C_76,A_74,B_75)
      | ~ v1_funct_1(C_76)
      | v1_xboole_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_223,plain,(
    ! [B_75,C_76] :
      ( k3_funct_2('#skF_2',B_75,C_76,'#skF_1'('#skF_2','#skF_3')) = k1_funct_1(C_76,'#skF_1'('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_75)))
      | ~ v1_funct_2(C_76,'#skF_2',B_75)
      | ~ v1_funct_1(C_76)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_188,c_219])).

tff(c_243,plain,(
    ! [B_83,C_84] :
      ( k3_funct_2('#skF_2',B_83,C_84,'#skF_1'('#skF_2','#skF_3')) = k1_funct_1(C_84,'#skF_1'('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_83)))
      | ~ v1_funct_2(C_84,'#skF_2',B_83)
      | ~ v1_funct_1(C_84) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_223])).

tff(c_246,plain,
    ( k3_funct_2('#skF_2','#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3')) = k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3'))
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_243])).

tff(c_249,plain,(
    k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) = '#skF_1'('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_192,c_246])).

tff(c_251,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_218,c_249])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:14:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.29  
% 2.08/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.30  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.08/1.30  
% 2.08/1.30  %Foreground sorts:
% 2.08/1.30  
% 2.08/1.30  
% 2.08/1.30  %Background operators:
% 2.08/1.30  
% 2.08/1.30  
% 2.08/1.30  %Foreground operators:
% 2.08/1.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.08/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.08/1.30  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.08/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.08/1.30  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.08/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.08/1.30  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.08/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.08/1.30  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.08/1.30  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.08/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.08/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.08/1.30  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.08/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.30  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.08/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.08/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.08/1.30  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.08/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.08/1.30  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 2.08/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.08/1.30  
% 2.37/1.31  tff(f_121, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => ((![C]: (m1_subset_1(C, A) => (k3_funct_2(A, A, B, C) = C))) => r2_funct_2(A, A, B, k6_partfun1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t201_funct_2)).
% 2.37/1.31  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.37/1.31  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.37/1.31  tff(f_74, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 2.37/1.31  tff(f_66, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.37/1.31  tff(f_89, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.37/1.31  tff(f_42, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_funct_1)).
% 2.37/1.31  tff(f_103, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_funct_2(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_funct_2)).
% 2.37/1.31  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 2.37/1.31  tff(f_87, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.37/1.31  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.37/1.31  tff(c_57, plain, (![C_37, A_38, B_39]: (v1_relat_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.37/1.31  tff(c_61, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_57])).
% 2.37/1.31  tff(c_40, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.37/1.31  tff(c_42, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.37/1.31  tff(c_68, plain, (![C_44, A_45, B_46]: (v4_relat_1(C_44, A_45) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.37/1.31  tff(c_72, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_36, c_68])).
% 2.37/1.31  tff(c_75, plain, (![B_49, A_50]: (k1_relat_1(B_49)=A_50 | ~v1_partfun1(B_49, A_50) | ~v4_relat_1(B_49, A_50) | ~v1_relat_1(B_49))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.37/1.31  tff(c_78, plain, (k1_relat_1('#skF_3')='#skF_2' | ~v1_partfun1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_75])).
% 2.37/1.31  tff(c_81, plain, (k1_relat_1('#skF_3')='#skF_2' | ~v1_partfun1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_61, c_78])).
% 2.37/1.31  tff(c_82, plain, (~v1_partfun1('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_81])).
% 2.37/1.31  tff(c_38, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.37/1.31  tff(c_83, plain, (![C_51, A_52, B_53]: (v1_partfun1(C_51, A_52) | ~v1_funct_2(C_51, A_52, B_53) | ~v1_funct_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))) | v1_xboole_0(B_53))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.37/1.31  tff(c_86, plain, (v1_partfun1('#skF_3', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_36, c_83])).
% 2.37/1.31  tff(c_89, plain, (v1_partfun1('#skF_3', '#skF_2') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_86])).
% 2.37/1.31  tff(c_91, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_82, c_89])).
% 2.37/1.31  tff(c_92, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_81])).
% 2.37/1.31  tff(c_28, plain, (![A_24]: (k6_relat_1(A_24)=k6_partfun1(A_24))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.37/1.31  tff(c_6, plain, (![B_4]: (r2_hidden('#skF_1'(k1_relat_1(B_4), B_4), k1_relat_1(B_4)) | k6_relat_1(k1_relat_1(B_4))=B_4 | ~v1_funct_1(B_4) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.37/1.31  tff(c_105, plain, (![B_56]: (r2_hidden('#skF_1'(k1_relat_1(B_56), B_56), k1_relat_1(B_56)) | k6_partfun1(k1_relat_1(B_56))=B_56 | ~v1_funct_1(B_56) | ~v1_relat_1(B_56))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_6])).
% 2.37/1.31  tff(c_111, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), k1_relat_1('#skF_3')) | k6_partfun1(k1_relat_1('#skF_3'))='#skF_3' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_92, c_105])).
% 2.37/1.31  tff(c_117, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | k6_partfun1('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_61, c_40, c_92, c_92, c_111])).
% 2.37/1.31  tff(c_128, plain, (k6_partfun1('#skF_2')='#skF_3'), inference(splitLeft, [status(thm)], [c_117])).
% 2.37/1.31  tff(c_32, plain, (~r2_funct_2('#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.37/1.31  tff(c_129, plain, (~r2_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_32])).
% 2.37/1.31  tff(c_169, plain, (![A_67, B_68, C_69, D_70]: (r2_funct_2(A_67, B_68, C_69, C_69) | ~m1_subset_1(D_70, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))) | ~v1_funct_2(D_70, A_67, B_68) | ~v1_funct_1(D_70) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))) | ~v1_funct_2(C_69, A_67, B_68) | ~v1_funct_1(C_69))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.37/1.31  tff(c_171, plain, (![C_69]: (r2_funct_2('#skF_2', '#skF_2', C_69, C_69) | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2(C_69, '#skF_2', '#skF_2') | ~v1_funct_1(C_69))), inference(resolution, [status(thm)], [c_36, c_169])).
% 2.37/1.31  tff(c_175, plain, (![C_71]: (r2_funct_2('#skF_2', '#skF_2', C_71, C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2(C_71, '#skF_2', '#skF_2') | ~v1_funct_1(C_71))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_171])).
% 2.37/1.31  tff(c_177, plain, (r2_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_175])).
% 2.37/1.31  tff(c_180, plain, (r2_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_177])).
% 2.37/1.31  tff(c_182, plain, $false, inference(negUnitSimplification, [status(thm)], [c_129, c_180])).
% 2.37/1.31  tff(c_184, plain, (k6_partfun1('#skF_2')!='#skF_3'), inference(splitRight, [status(thm)], [c_117])).
% 2.37/1.31  tff(c_4, plain, (![B_4]: (k1_funct_1(B_4, '#skF_1'(k1_relat_1(B_4), B_4))!='#skF_1'(k1_relat_1(B_4), B_4) | k6_relat_1(k1_relat_1(B_4))=B_4 | ~v1_funct_1(B_4) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.37/1.31  tff(c_212, plain, (![B_73]: (k1_funct_1(B_73, '#skF_1'(k1_relat_1(B_73), B_73))!='#skF_1'(k1_relat_1(B_73), B_73) | k6_partfun1(k1_relat_1(B_73))=B_73 | ~v1_funct_1(B_73) | ~v1_relat_1(B_73))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_4])).
% 2.37/1.31  tff(c_215, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))!='#skF_1'(k1_relat_1('#skF_3'), '#skF_3') | k6_partfun1(k1_relat_1('#skF_3'))='#skF_3' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_92, c_212])).
% 2.37/1.31  tff(c_217, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))!='#skF_1'('#skF_2', '#skF_3') | k6_partfun1('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_61, c_40, c_92, c_92, c_215])).
% 2.37/1.31  tff(c_218, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))!='#skF_1'('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_184, c_217])).
% 2.37/1.31  tff(c_183, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_117])).
% 2.37/1.31  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.37/1.31  tff(c_188, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_183, c_2])).
% 2.37/1.31  tff(c_34, plain, (![C_33]: (k3_funct_2('#skF_2', '#skF_2', '#skF_3', C_33)=C_33 | ~m1_subset_1(C_33, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.37/1.31  tff(c_192, plain, (k3_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3'))='#skF_1'('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_188, c_34])).
% 2.37/1.31  tff(c_219, plain, (![A_74, B_75, C_76, D_77]: (k3_funct_2(A_74, B_75, C_76, D_77)=k1_funct_1(C_76, D_77) | ~m1_subset_1(D_77, A_74) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))) | ~v1_funct_2(C_76, A_74, B_75) | ~v1_funct_1(C_76) | v1_xboole_0(A_74))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.37/1.31  tff(c_223, plain, (![B_75, C_76]: (k3_funct_2('#skF_2', B_75, C_76, '#skF_1'('#skF_2', '#skF_3'))=k1_funct_1(C_76, '#skF_1'('#skF_2', '#skF_3')) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_75))) | ~v1_funct_2(C_76, '#skF_2', B_75) | ~v1_funct_1(C_76) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_188, c_219])).
% 2.37/1.31  tff(c_243, plain, (![B_83, C_84]: (k3_funct_2('#skF_2', B_83, C_84, '#skF_1'('#skF_2', '#skF_3'))=k1_funct_1(C_84, '#skF_1'('#skF_2', '#skF_3')) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_83))) | ~v1_funct_2(C_84, '#skF_2', B_83) | ~v1_funct_1(C_84))), inference(negUnitSimplification, [status(thm)], [c_42, c_223])).
% 2.37/1.31  tff(c_246, plain, (k3_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3'))=k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3')) | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_243])).
% 2.37/1.31  tff(c_249, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))='#skF_1'('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_192, c_246])).
% 2.37/1.31  tff(c_251, plain, $false, inference(negUnitSimplification, [status(thm)], [c_218, c_249])).
% 2.37/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.31  
% 2.37/1.31  Inference rules
% 2.37/1.31  ----------------------
% 2.37/1.31  #Ref     : 0
% 2.37/1.31  #Sup     : 38
% 2.37/1.31  #Fact    : 0
% 2.37/1.31  #Define  : 0
% 2.37/1.31  #Split   : 2
% 2.37/1.31  #Chain   : 0
% 2.37/1.31  #Close   : 0
% 2.37/1.31  
% 2.37/1.31  Ordering : KBO
% 2.37/1.31  
% 2.37/1.31  Simplification rules
% 2.37/1.31  ----------------------
% 2.37/1.31  #Subsume      : 0
% 2.37/1.31  #Demod        : 78
% 2.37/1.31  #Tautology    : 19
% 2.37/1.31  #SimpNegUnit  : 9
% 2.37/1.31  #BackRed      : 1
% 2.37/1.31  
% 2.37/1.31  #Partial instantiations: 0
% 2.37/1.31  #Strategies tried      : 1
% 2.37/1.31  
% 2.37/1.31  Timing (in seconds)
% 2.37/1.31  ----------------------
% 2.37/1.32  Preprocessing        : 0.32
% 2.37/1.32  Parsing              : 0.17
% 2.37/1.32  CNF conversion       : 0.02
% 2.37/1.32  Main loop            : 0.20
% 2.37/1.32  Inferencing          : 0.07
% 2.37/1.32  Reduction            : 0.07
% 2.37/1.32  Demodulation         : 0.05
% 2.37/1.32  BG Simplification    : 0.02
% 2.37/1.32  Subsumption          : 0.02
% 2.37/1.32  Abstraction          : 0.01
% 2.37/1.32  MUC search           : 0.00
% 2.37/1.32  Cooper               : 0.00
% 2.37/1.32  Total                : 0.55
% 2.37/1.32  Index Insertion      : 0.00
% 2.37/1.32  Index Deletion       : 0.00
% 2.37/1.32  Index Matching       : 0.00
% 2.37/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
