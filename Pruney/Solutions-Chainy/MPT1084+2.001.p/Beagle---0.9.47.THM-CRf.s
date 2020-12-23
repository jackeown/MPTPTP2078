%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:19 EST 2020

% Result     : Theorem 3.46s
% Output     : CNFRefutation 3.46s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 464 expanded)
%              Number of leaves         :   36 ( 172 expanded)
%              Depth                    :   13
%              Number of atoms          :  186 (1272 expanded)
%              Number of equality atoms :   34 ( 215 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_133,negated_conjecture,(
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

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_101,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_115,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_funct_2(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_99,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_75,plain,(
    ! [C_45,A_46,B_47] :
      ( v1_relat_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_84,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_75])).

tff(c_48,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_123,plain,(
    ! [C_61,A_62,B_63] :
      ( v4_relat_1(C_61,A_62)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_132,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_123])).

tff(c_156,plain,(
    ! [B_79,A_80] :
      ( k1_relat_1(B_79) = A_80
      | ~ v1_partfun1(B_79,A_80)
      | ~ v4_relat_1(B_79,A_80)
      | ~ v1_relat_1(B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_159,plain,
    ( k1_relat_1('#skF_3') = '#skF_2'
    | ~ v1_partfun1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_132,c_156])).

tff(c_162,plain,
    ( k1_relat_1('#skF_3') = '#skF_2'
    | ~ v1_partfun1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_159])).

tff(c_163,plain,(
    ~ v1_partfun1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_162])).

tff(c_46,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_171,plain,(
    ! [C_90,A_91,B_92] :
      ( v1_partfun1(C_90,A_91)
      | ~ v1_funct_2(C_90,A_91,B_92)
      | ~ v1_funct_1(C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92)))
      | v1_xboole_0(B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_178,plain,
    ( v1_partfun1('#skF_3','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_171])).

tff(c_182,plain,
    ( v1_partfun1('#skF_3','#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_178])).

tff(c_184,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_163,c_182])).

tff(c_185,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_36,plain,(
    ! [A_29] : k6_relat_1(A_29) = k6_partfun1(A_29) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_14,plain,(
    ! [B_9] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_9),B_9),k1_relat_1(B_9))
      | k6_relat_1(k1_relat_1(B_9)) = B_9
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_260,plain,(
    ! [B_104] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_104),B_104),k1_relat_1(B_104))
      | k6_partfun1(k1_relat_1(B_104)) = B_104
      | ~ v1_funct_1(B_104)
      | ~ v1_relat_1(B_104) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_14])).

tff(c_265,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),k1_relat_1('#skF_3'))
    | k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_260])).

tff(c_271,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | k6_partfun1('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_48,c_185,c_185,c_265])).

tff(c_274,plain,(
    k6_partfun1('#skF_2') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_271])).

tff(c_40,plain,(
    ~ r2_funct_2('#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_275,plain,(
    ~ r2_funct_2('#skF_2','#skF_2','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_40])).

tff(c_448,plain,(
    ! [A_134,B_135,C_136,D_137] :
      ( r2_funct_2(A_134,B_135,C_136,C_136)
      | ~ m1_subset_1(D_137,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135)))
      | ~ v1_funct_2(D_137,A_134,B_135)
      | ~ v1_funct_1(D_137)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135)))
      | ~ v1_funct_2(C_136,A_134,B_135)
      | ~ v1_funct_1(C_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_456,plain,(
    ! [C_136] :
      ( r2_funct_2('#skF_2','#skF_2',C_136,C_136)
      | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
      | ~ v1_funct_2(C_136,'#skF_2','#skF_2')
      | ~ v1_funct_1(C_136) ) ),
    inference(resolution,[status(thm)],[c_44,c_448])).

tff(c_462,plain,(
    ! [C_138] :
      ( r2_funct_2('#skF_2','#skF_2',C_138,C_138)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
      | ~ v1_funct_2(C_138,'#skF_2','#skF_2')
      | ~ v1_funct_1(C_138) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_456])).

tff(c_470,plain,
    ( r2_funct_2('#skF_2','#skF_2','#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_462])).

tff(c_475,plain,(
    r2_funct_2('#skF_2','#skF_2','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_470])).

tff(c_477,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_275,c_475])).

tff(c_479,plain,(
    k6_partfun1('#skF_2') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_271])).

tff(c_12,plain,(
    ! [B_9] :
      ( k1_funct_1(B_9,'#skF_1'(k1_relat_1(B_9),B_9)) != '#skF_1'(k1_relat_1(B_9),B_9)
      | k6_relat_1(k1_relat_1(B_9)) = B_9
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_576,plain,(
    ! [B_151] :
      ( k1_funct_1(B_151,'#skF_1'(k1_relat_1(B_151),B_151)) != '#skF_1'(k1_relat_1(B_151),B_151)
      | k6_partfun1(k1_relat_1(B_151)) = B_151
      | ~ v1_funct_1(B_151)
      | ~ v1_relat_1(B_151) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_12])).

tff(c_579,plain,
    ( k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) != '#skF_1'(k1_relat_1('#skF_3'),'#skF_3')
    | k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_576])).

tff(c_581,plain,
    ( k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) != '#skF_1'('#skF_2','#skF_3')
    | k6_partfun1('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_48,c_185,c_185,c_579])).

tff(c_582,plain,(
    k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) != '#skF_1'('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_479,c_581])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(B_7),A_6)
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_194,plain,(
    ! [A_6] :
      ( r1_tarski('#skF_2',A_6)
      | ~ v4_relat_1('#skF_3',A_6)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_10])).

tff(c_229,plain,(
    ! [A_96] :
      ( r1_tarski('#skF_2',A_96)
      | ~ v4_relat_1('#skF_3',A_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_194])).

tff(c_237,plain,(
    r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_132,c_229])).

tff(c_478,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_271])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_145,plain,(
    ! [A_68,C_69,B_70] :
      ( m1_subset_1(A_68,C_69)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(C_69))
      | ~ r2_hidden(A_68,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_150,plain,(
    ! [A_68,B_2,A_1] :
      ( m1_subset_1(A_68,B_2)
      | ~ r2_hidden(A_68,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_145])).

tff(c_485,plain,(
    ! [B_139] :
      ( m1_subset_1('#skF_1'('#skF_2','#skF_3'),B_139)
      | ~ r1_tarski('#skF_2',B_139) ) ),
    inference(resolution,[status(thm)],[c_478,c_150])).

tff(c_42,plain,(
    ! [C_38] :
      ( k3_funct_2('#skF_2','#skF_2','#skF_3',C_38) = C_38
      | ~ m1_subset_1(C_38,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_504,plain,
    ( k3_funct_2('#skF_2','#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3')) = '#skF_1'('#skF_2','#skF_3')
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_485,c_42])).

tff(c_515,plain,(
    k3_funct_2('#skF_2','#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3')) = '#skF_1'('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_504])).

tff(c_482,plain,(
    ! [B_2] :
      ( m1_subset_1('#skF_1'('#skF_2','#skF_3'),B_2)
      | ~ r1_tarski('#skF_2',B_2) ) ),
    inference(resolution,[status(thm)],[c_478,c_150])).

tff(c_583,plain,(
    ! [A_152,B_153,C_154,D_155] :
      ( k3_funct_2(A_152,B_153,C_154,D_155) = k1_funct_1(C_154,D_155)
      | ~ m1_subset_1(D_155,A_152)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(A_152,B_153)))
      | ~ v1_funct_2(C_154,A_152,B_153)
      | ~ v1_funct_1(C_154)
      | v1_xboole_0(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_883,plain,(
    ! [B_212,B_213,C_214] :
      ( k3_funct_2(B_212,B_213,C_214,'#skF_1'('#skF_2','#skF_3')) = k1_funct_1(C_214,'#skF_1'('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_214,k1_zfmisc_1(k2_zfmisc_1(B_212,B_213)))
      | ~ v1_funct_2(C_214,B_212,B_213)
      | ~ v1_funct_1(C_214)
      | v1_xboole_0(B_212)
      | ~ r1_tarski('#skF_2',B_212) ) ),
    inference(resolution,[status(thm)],[c_482,c_583])).

tff(c_898,plain,
    ( k3_funct_2('#skF_2','#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3')) = k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3'))
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_2')
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_883])).

tff(c_904,plain,
    ( k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) = '#skF_1'('#skF_2','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_48,c_46,c_515,c_898])).

tff(c_906,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_582,c_904])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:12:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.46/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/1.57  
% 3.46/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/1.57  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.46/1.57  
% 3.46/1.57  %Foreground sorts:
% 3.46/1.57  
% 3.46/1.57  
% 3.46/1.57  %Background operators:
% 3.46/1.57  
% 3.46/1.57  
% 3.46/1.57  %Foreground operators:
% 3.46/1.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.46/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.46/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.46/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.46/1.57  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.46/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.46/1.57  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.46/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.46/1.57  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.46/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.46/1.57  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.46/1.57  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.46/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.46/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.46/1.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.46/1.57  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.46/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.46/1.57  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.46/1.57  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.46/1.57  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.46/1.57  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 3.46/1.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.46/1.57  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 3.46/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.46/1.57  
% 3.46/1.59  tff(f_133, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => ((![C]: (m1_subset_1(C, A) => (k3_funct_2(A, A, B, C) = C))) => r2_funct_2(A, A, B, k6_partfun1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t201_funct_2)).
% 3.46/1.59  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.46/1.59  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.46/1.59  tff(f_86, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 3.46/1.59  tff(f_78, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 3.46/1.59  tff(f_101, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.46/1.59  tff(f_54, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_funct_1)).
% 3.46/1.59  tff(f_115, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_funct_2(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_funct_2)).
% 3.46/1.59  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.46/1.59  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.46/1.59  tff(f_35, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.46/1.59  tff(f_99, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 3.46/1.59  tff(c_50, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.46/1.59  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.46/1.59  tff(c_75, plain, (![C_45, A_46, B_47]: (v1_relat_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.46/1.59  tff(c_84, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_75])).
% 3.46/1.59  tff(c_48, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.46/1.59  tff(c_123, plain, (![C_61, A_62, B_63]: (v4_relat_1(C_61, A_62) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.46/1.59  tff(c_132, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_123])).
% 3.46/1.59  tff(c_156, plain, (![B_79, A_80]: (k1_relat_1(B_79)=A_80 | ~v1_partfun1(B_79, A_80) | ~v4_relat_1(B_79, A_80) | ~v1_relat_1(B_79))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.46/1.59  tff(c_159, plain, (k1_relat_1('#skF_3')='#skF_2' | ~v1_partfun1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_132, c_156])).
% 3.46/1.59  tff(c_162, plain, (k1_relat_1('#skF_3')='#skF_2' | ~v1_partfun1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_159])).
% 3.46/1.59  tff(c_163, plain, (~v1_partfun1('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_162])).
% 3.46/1.59  tff(c_46, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.46/1.59  tff(c_171, plain, (![C_90, A_91, B_92]: (v1_partfun1(C_90, A_91) | ~v1_funct_2(C_90, A_91, B_92) | ~v1_funct_1(C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))) | v1_xboole_0(B_92))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.46/1.59  tff(c_178, plain, (v1_partfun1('#skF_3', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_171])).
% 3.46/1.59  tff(c_182, plain, (v1_partfun1('#skF_3', '#skF_2') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_178])).
% 3.46/1.59  tff(c_184, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_163, c_182])).
% 3.46/1.59  tff(c_185, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_162])).
% 3.46/1.59  tff(c_36, plain, (![A_29]: (k6_relat_1(A_29)=k6_partfun1(A_29))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.46/1.59  tff(c_14, plain, (![B_9]: (r2_hidden('#skF_1'(k1_relat_1(B_9), B_9), k1_relat_1(B_9)) | k6_relat_1(k1_relat_1(B_9))=B_9 | ~v1_funct_1(B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.46/1.59  tff(c_260, plain, (![B_104]: (r2_hidden('#skF_1'(k1_relat_1(B_104), B_104), k1_relat_1(B_104)) | k6_partfun1(k1_relat_1(B_104))=B_104 | ~v1_funct_1(B_104) | ~v1_relat_1(B_104))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_14])).
% 3.46/1.59  tff(c_265, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), k1_relat_1('#skF_3')) | k6_partfun1(k1_relat_1('#skF_3'))='#skF_3' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_185, c_260])).
% 3.46/1.59  tff(c_271, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | k6_partfun1('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_48, c_185, c_185, c_265])).
% 3.46/1.59  tff(c_274, plain, (k6_partfun1('#skF_2')='#skF_3'), inference(splitLeft, [status(thm)], [c_271])).
% 3.46/1.59  tff(c_40, plain, (~r2_funct_2('#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.46/1.59  tff(c_275, plain, (~r2_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_274, c_40])).
% 3.46/1.59  tff(c_448, plain, (![A_134, B_135, C_136, D_137]: (r2_funct_2(A_134, B_135, C_136, C_136) | ~m1_subset_1(D_137, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))) | ~v1_funct_2(D_137, A_134, B_135) | ~v1_funct_1(D_137) | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))) | ~v1_funct_2(C_136, A_134, B_135) | ~v1_funct_1(C_136))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.46/1.59  tff(c_456, plain, (![C_136]: (r2_funct_2('#skF_2', '#skF_2', C_136, C_136) | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2(C_136, '#skF_2', '#skF_2') | ~v1_funct_1(C_136))), inference(resolution, [status(thm)], [c_44, c_448])).
% 3.46/1.59  tff(c_462, plain, (![C_138]: (r2_funct_2('#skF_2', '#skF_2', C_138, C_138) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2(C_138, '#skF_2', '#skF_2') | ~v1_funct_1(C_138))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_456])).
% 3.46/1.59  tff(c_470, plain, (r2_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_462])).
% 3.46/1.59  tff(c_475, plain, (r2_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_470])).
% 3.46/1.59  tff(c_477, plain, $false, inference(negUnitSimplification, [status(thm)], [c_275, c_475])).
% 3.46/1.59  tff(c_479, plain, (k6_partfun1('#skF_2')!='#skF_3'), inference(splitRight, [status(thm)], [c_271])).
% 3.46/1.59  tff(c_12, plain, (![B_9]: (k1_funct_1(B_9, '#skF_1'(k1_relat_1(B_9), B_9))!='#skF_1'(k1_relat_1(B_9), B_9) | k6_relat_1(k1_relat_1(B_9))=B_9 | ~v1_funct_1(B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.46/1.59  tff(c_576, plain, (![B_151]: (k1_funct_1(B_151, '#skF_1'(k1_relat_1(B_151), B_151))!='#skF_1'(k1_relat_1(B_151), B_151) | k6_partfun1(k1_relat_1(B_151))=B_151 | ~v1_funct_1(B_151) | ~v1_relat_1(B_151))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_12])).
% 3.46/1.59  tff(c_579, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))!='#skF_1'(k1_relat_1('#skF_3'), '#skF_3') | k6_partfun1(k1_relat_1('#skF_3'))='#skF_3' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_185, c_576])).
% 3.46/1.59  tff(c_581, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))!='#skF_1'('#skF_2', '#skF_3') | k6_partfun1('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_48, c_185, c_185, c_579])).
% 3.46/1.59  tff(c_582, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))!='#skF_1'('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_479, c_581])).
% 3.46/1.59  tff(c_10, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(B_7), A_6) | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.46/1.59  tff(c_194, plain, (![A_6]: (r1_tarski('#skF_2', A_6) | ~v4_relat_1('#skF_3', A_6) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_185, c_10])).
% 3.46/1.59  tff(c_229, plain, (![A_96]: (r1_tarski('#skF_2', A_96) | ~v4_relat_1('#skF_3', A_96))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_194])).
% 3.46/1.59  tff(c_237, plain, (r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_132, c_229])).
% 3.46/1.59  tff(c_478, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_271])).
% 3.46/1.59  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.46/1.59  tff(c_145, plain, (![A_68, C_69, B_70]: (m1_subset_1(A_68, C_69) | ~m1_subset_1(B_70, k1_zfmisc_1(C_69)) | ~r2_hidden(A_68, B_70))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.46/1.59  tff(c_150, plain, (![A_68, B_2, A_1]: (m1_subset_1(A_68, B_2) | ~r2_hidden(A_68, A_1) | ~r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_4, c_145])).
% 3.46/1.59  tff(c_485, plain, (![B_139]: (m1_subset_1('#skF_1'('#skF_2', '#skF_3'), B_139) | ~r1_tarski('#skF_2', B_139))), inference(resolution, [status(thm)], [c_478, c_150])).
% 3.46/1.59  tff(c_42, plain, (![C_38]: (k3_funct_2('#skF_2', '#skF_2', '#skF_3', C_38)=C_38 | ~m1_subset_1(C_38, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.46/1.59  tff(c_504, plain, (k3_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3'))='#skF_1'('#skF_2', '#skF_3') | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_485, c_42])).
% 3.46/1.59  tff(c_515, plain, (k3_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3'))='#skF_1'('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_237, c_504])).
% 3.46/1.59  tff(c_482, plain, (![B_2]: (m1_subset_1('#skF_1'('#skF_2', '#skF_3'), B_2) | ~r1_tarski('#skF_2', B_2))), inference(resolution, [status(thm)], [c_478, c_150])).
% 3.46/1.59  tff(c_583, plain, (![A_152, B_153, C_154, D_155]: (k3_funct_2(A_152, B_153, C_154, D_155)=k1_funct_1(C_154, D_155) | ~m1_subset_1(D_155, A_152) | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(A_152, B_153))) | ~v1_funct_2(C_154, A_152, B_153) | ~v1_funct_1(C_154) | v1_xboole_0(A_152))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.46/1.59  tff(c_883, plain, (![B_212, B_213, C_214]: (k3_funct_2(B_212, B_213, C_214, '#skF_1'('#skF_2', '#skF_3'))=k1_funct_1(C_214, '#skF_1'('#skF_2', '#skF_3')) | ~m1_subset_1(C_214, k1_zfmisc_1(k2_zfmisc_1(B_212, B_213))) | ~v1_funct_2(C_214, B_212, B_213) | ~v1_funct_1(C_214) | v1_xboole_0(B_212) | ~r1_tarski('#skF_2', B_212))), inference(resolution, [status(thm)], [c_482, c_583])).
% 3.46/1.59  tff(c_898, plain, (k3_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3'))=k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3')) | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_2') | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_883])).
% 3.46/1.59  tff(c_904, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))='#skF_1'('#skF_2', '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_237, c_48, c_46, c_515, c_898])).
% 3.46/1.59  tff(c_906, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_582, c_904])).
% 3.46/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/1.59  
% 3.46/1.59  Inference rules
% 3.46/1.59  ----------------------
% 3.46/1.59  #Ref     : 0
% 3.46/1.59  #Sup     : 164
% 3.46/1.59  #Fact    : 0
% 3.46/1.59  #Define  : 0
% 3.46/1.59  #Split   : 7
% 3.46/1.59  #Chain   : 0
% 3.46/1.59  #Close   : 0
% 3.46/1.59  
% 3.46/1.59  Ordering : KBO
% 3.46/1.59  
% 3.46/1.59  Simplification rules
% 3.46/1.59  ----------------------
% 3.46/1.59  #Subsume      : 35
% 3.46/1.59  #Demod        : 186
% 3.46/1.59  #Tautology    : 39
% 3.46/1.59  #SimpNegUnit  : 19
% 3.46/1.59  #BackRed      : 1
% 3.46/1.59  
% 3.46/1.59  #Partial instantiations: 0
% 3.46/1.59  #Strategies tried      : 1
% 3.46/1.59  
% 3.46/1.59  Timing (in seconds)
% 3.46/1.59  ----------------------
% 3.46/1.59  Preprocessing        : 0.32
% 3.46/1.59  Parsing              : 0.17
% 3.46/1.59  CNF conversion       : 0.02
% 3.46/1.59  Main loop            : 0.43
% 3.46/1.59  Inferencing          : 0.16
% 3.46/1.59  Reduction            : 0.13
% 3.46/1.59  Demodulation         : 0.09
% 3.46/1.59  BG Simplification    : 0.02
% 3.46/1.59  Subsumption          : 0.08
% 3.46/1.59  Abstraction          : 0.02
% 3.46/1.59  MUC search           : 0.00
% 3.46/1.59  Cooper               : 0.00
% 3.46/1.59  Total                : 0.79
% 3.46/1.59  Index Insertion      : 0.00
% 3.46/1.59  Index Deletion       : 0.00
% 3.46/1.59  Index Matching       : 0.00
% 3.46/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
