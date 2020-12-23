%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:19 EST 2020

% Result     : Theorem 2.56s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 176 expanded)
%              Number of leaves         :   35 (  74 expanded)
%              Depth                    :   11
%              Number of atoms          :  145 ( 364 expanded)
%              Number of equality atoms :   21 (  43 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_121,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
               => ~ ( k1_relset_1(A,B,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k2_relset_1(A,B,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relset_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_78,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_86,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_410,plain,(
    ! [A_123,B_124,C_125] :
      ( k1_relset_1(A_123,B_124,C_125) = k1_relat_1(C_125)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_123,B_124))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_424,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_410])).

tff(c_36,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_425,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_424,c_36])).

tff(c_22,plain,(
    ! [A_17,B_18] : v1_relat_1(k2_zfmisc_1(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_316,plain,(
    ! [B_96,A_97] :
      ( v1_relat_1(B_96)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(A_97))
      | ~ v1_relat_1(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_319,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_38,c_316])).

tff(c_322,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_319])).

tff(c_98,plain,(
    ! [B_55,A_56] :
      ( v1_relat_1(B_55)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_56))
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_101,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_38,c_98])).

tff(c_104,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_101])).

tff(c_171,plain,(
    ! [C_73,B_74,A_75] :
      ( v5_relat_1(C_73,B_74)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_75,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_185,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_171])).

tff(c_18,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k2_relat_1(B_15),A_14)
      | ~ v5_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_212,plain,(
    ! [A_86,B_87,C_88] :
      ( k2_relset_1(A_86,B_87,C_88) = k2_relat_1(C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_226,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_212])).

tff(c_105,plain,(
    ! [A_57,B_58] :
      ( r2_hidden('#skF_1'(A_57,B_58),B_58)
      | r1_xboole_0(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_118,plain,(
    ! [A_62,B_63] :
      ( m1_subset_1('#skF_1'(A_62,B_63),B_63)
      | r1_xboole_0(A_62,B_63) ) ),
    inference(resolution,[status(thm)],[c_105,c_12])).

tff(c_88,plain,(
    ! [A_53,B_54] :
      ( r2_hidden('#skF_1'(A_53,B_54),A_53)
      | r1_xboole_0(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_34,plain,(
    ! [D_40] :
      ( ~ r2_hidden(D_40,k2_relset_1('#skF_2','#skF_3','#skF_4'))
      | ~ m1_subset_1(D_40,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_96,plain,(
    ! [B_54] :
      ( ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_2','#skF_3','#skF_4'),B_54),'#skF_3')
      | r1_xboole_0(k2_relset_1('#skF_2','#skF_3','#skF_4'),B_54) ) ),
    inference(resolution,[status(thm)],[c_88,c_34])).

tff(c_127,plain,(
    r1_xboole_0(k2_relset_1('#skF_2','#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_118,c_96])).

tff(c_233,plain,(
    r1_xboole_0(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_127])).

tff(c_20,plain,(
    ! [A_16] :
      ( v1_xboole_0(k1_relat_1(A_16))
      | ~ v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_45,plain,(
    ! [A_44] :
      ( v1_xboole_0(k1_relat_1(A_44))
      | ~ v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_50,plain,(
    ! [A_45] :
      ( k1_relat_1(A_45) = k1_xboole_0
      | ~ v1_xboole_0(A_45) ) ),
    inference(resolution,[status(thm)],[c_45,c_2])).

tff(c_57,plain,(
    ! [A_49] :
      ( k1_relat_1(k1_relat_1(A_49)) = k1_xboole_0
      | ~ v1_xboole_0(A_49) ) ),
    inference(resolution,[status(thm)],[c_20,c_50])).

tff(c_66,plain,(
    ! [A_49] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(k1_relat_1(A_49))
      | ~ v1_xboole_0(A_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_20])).

tff(c_77,plain,(
    ! [A_51] :
      ( ~ v1_xboole_0(k1_relat_1(A_51))
      | ~ v1_xboole_0(A_51) ) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_84,plain,(
    ! [A_16] : ~ v1_xboole_0(A_16) ),
    inference(resolution,[status(thm)],[c_20,c_77])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( ~ r1_xboole_0(B_8,A_7)
      | ~ r1_tarski(B_8,A_7)
      | v1_xboole_0(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_116,plain,(
    ! [B_8,A_7] :
      ( ~ r1_xboole_0(B_8,A_7)
      | ~ r1_tarski(B_8,A_7) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_10])).

tff(c_268,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_233,c_116])).

tff(c_276,plain,
    ( ~ v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_268])).

tff(c_280,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_185,c_276])).

tff(c_281,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_367,plain,(
    ! [C_112,B_113,A_114] :
      ( v5_relat_1(C_112,B_113)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_114,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_381,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_367])).

tff(c_446,plain,(
    ! [A_127,B_128,C_129] :
      ( k2_relset_1(A_127,B_128,C_129) = k2_relat_1(C_129)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_460,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_446])).

tff(c_323,plain,(
    ! [A_98,B_99] :
      ( r2_hidden('#skF_1'(A_98,B_99),B_99)
      | r1_xboole_0(A_98,B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_340,plain,(
    ! [A_103,B_104] :
      ( m1_subset_1('#skF_1'(A_103,B_104),B_104)
      | r1_xboole_0(A_103,B_104) ) ),
    inference(resolution,[status(thm)],[c_323,c_12])).

tff(c_305,plain,(
    ! [A_92,B_93] :
      ( r2_hidden('#skF_1'(A_92,B_93),A_92)
      | r1_xboole_0(A_92,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_313,plain,(
    ! [B_93] :
      ( ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_2','#skF_3','#skF_4'),B_93),'#skF_3')
      | r1_xboole_0(k2_relset_1('#skF_2','#skF_3','#skF_4'),B_93) ) ),
    inference(resolution,[status(thm)],[c_305,c_34])).

tff(c_349,plain,(
    r1_xboole_0(k2_relset_1('#skF_2','#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_340,c_313])).

tff(c_354,plain,
    ( ~ r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),'#skF_3')
    | v1_xboole_0(k2_relset_1('#skF_2','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_349,c_10])).

tff(c_430,plain,(
    ~ r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_354])).

tff(c_461,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_460,c_430])).

tff(c_502,plain,
    ( ~ v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_461])).

tff(c_506,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_381,c_502])).

tff(c_507,plain,(
    v1_xboole_0(k2_relset_1('#skF_2','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_354])).

tff(c_516,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_507,c_2])).

tff(c_536,plain,(
    ! [A_131,B_132,C_133] :
      ( k2_relset_1(A_131,B_132,C_133) = k2_relat_1(C_133)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_547,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_536])).

tff(c_551,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_516,c_547])).

tff(c_24,plain,(
    ! [A_19] :
      ( ~ v1_xboole_0(k2_relat_1(A_19))
      | ~ v1_relat_1(A_19)
      | v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_561,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_551,c_24])).

tff(c_569,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_281,c_561])).

tff(c_49,plain,(
    ! [A_44] :
      ( k1_relat_1(A_44) = k1_xboole_0
      | ~ v1_xboole_0(A_44) ) ),
    inference(resolution,[status(thm)],[c_45,c_2])).

tff(c_573,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_569,c_49])).

tff(c_580,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_425,c_573])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:00:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.56/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.42  
% 2.56/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.42  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.56/1.42  
% 2.56/1.42  %Foreground sorts:
% 2.56/1.42  
% 2.56/1.42  
% 2.56/1.42  %Background operators:
% 2.56/1.42  
% 2.56/1.42  
% 2.56/1.42  %Foreground operators:
% 2.56/1.42  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.56/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.56/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.56/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.56/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.56/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.56/1.42  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.56/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.56/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.56/1.42  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.56/1.42  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.56/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.56/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.56/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.56/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.56/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.56/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.56/1.42  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.56/1.42  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.56/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.56/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.56/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.56/1.42  
% 2.56/1.44  tff(f_121, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_relset_1)).
% 2.56/1.44  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.56/1.44  tff(f_78, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.56/1.44  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.56/1.44  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.56/1.44  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.56/1.44  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.56/1.44  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.56/1.44  tff(f_59, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 2.56/1.44  tff(f_76, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_relat_1)).
% 2.56/1.44  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.56/1.44  tff(f_55, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.56/1.44  tff(f_86, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 2.56/1.44  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.56/1.44  tff(c_410, plain, (![A_123, B_124, C_125]: (k1_relset_1(A_123, B_124, C_125)=k1_relat_1(C_125) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(A_123, B_124))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.56/1.44  tff(c_424, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_410])).
% 2.56/1.44  tff(c_36, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.56/1.44  tff(c_425, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_424, c_36])).
% 2.56/1.44  tff(c_22, plain, (![A_17, B_18]: (v1_relat_1(k2_zfmisc_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.56/1.44  tff(c_316, plain, (![B_96, A_97]: (v1_relat_1(B_96) | ~m1_subset_1(B_96, k1_zfmisc_1(A_97)) | ~v1_relat_1(A_97))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.56/1.44  tff(c_319, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_38, c_316])).
% 2.56/1.44  tff(c_322, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_319])).
% 2.56/1.44  tff(c_98, plain, (![B_55, A_56]: (v1_relat_1(B_55) | ~m1_subset_1(B_55, k1_zfmisc_1(A_56)) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.56/1.44  tff(c_101, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_38, c_98])).
% 2.56/1.44  tff(c_104, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_101])).
% 2.56/1.44  tff(c_171, plain, (![C_73, B_74, A_75]: (v5_relat_1(C_73, B_74) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_75, B_74))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.56/1.44  tff(c_185, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_171])).
% 2.56/1.44  tff(c_18, plain, (![B_15, A_14]: (r1_tarski(k2_relat_1(B_15), A_14) | ~v5_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.56/1.44  tff(c_212, plain, (![A_86, B_87, C_88]: (k2_relset_1(A_86, B_87, C_88)=k2_relat_1(C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.56/1.44  tff(c_226, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_212])).
% 2.56/1.44  tff(c_105, plain, (![A_57, B_58]: (r2_hidden('#skF_1'(A_57, B_58), B_58) | r1_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.56/1.44  tff(c_12, plain, (![A_9, B_10]: (m1_subset_1(A_9, B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.56/1.44  tff(c_118, plain, (![A_62, B_63]: (m1_subset_1('#skF_1'(A_62, B_63), B_63) | r1_xboole_0(A_62, B_63))), inference(resolution, [status(thm)], [c_105, c_12])).
% 2.56/1.44  tff(c_88, plain, (![A_53, B_54]: (r2_hidden('#skF_1'(A_53, B_54), A_53) | r1_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.56/1.44  tff(c_34, plain, (![D_40]: (~r2_hidden(D_40, k2_relset_1('#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1(D_40, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.56/1.44  tff(c_96, plain, (![B_54]: (~m1_subset_1('#skF_1'(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), B_54), '#skF_3') | r1_xboole_0(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), B_54))), inference(resolution, [status(thm)], [c_88, c_34])).
% 2.56/1.44  tff(c_127, plain, (r1_xboole_0(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_118, c_96])).
% 2.56/1.44  tff(c_233, plain, (r1_xboole_0(k2_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_226, c_127])).
% 2.56/1.44  tff(c_20, plain, (![A_16]: (v1_xboole_0(k1_relat_1(A_16)) | ~v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.56/1.44  tff(c_45, plain, (![A_44]: (v1_xboole_0(k1_relat_1(A_44)) | ~v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.56/1.44  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.56/1.44  tff(c_50, plain, (![A_45]: (k1_relat_1(A_45)=k1_xboole_0 | ~v1_xboole_0(A_45))), inference(resolution, [status(thm)], [c_45, c_2])).
% 2.56/1.44  tff(c_57, plain, (![A_49]: (k1_relat_1(k1_relat_1(A_49))=k1_xboole_0 | ~v1_xboole_0(A_49))), inference(resolution, [status(thm)], [c_20, c_50])).
% 2.56/1.44  tff(c_66, plain, (![A_49]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(k1_relat_1(A_49)) | ~v1_xboole_0(A_49))), inference(superposition, [status(thm), theory('equality')], [c_57, c_20])).
% 2.56/1.44  tff(c_77, plain, (![A_51]: (~v1_xboole_0(k1_relat_1(A_51)) | ~v1_xboole_0(A_51))), inference(splitLeft, [status(thm)], [c_66])).
% 2.56/1.44  tff(c_84, plain, (![A_16]: (~v1_xboole_0(A_16))), inference(resolution, [status(thm)], [c_20, c_77])).
% 2.56/1.44  tff(c_10, plain, (![B_8, A_7]: (~r1_xboole_0(B_8, A_7) | ~r1_tarski(B_8, A_7) | v1_xboole_0(B_8))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.56/1.44  tff(c_116, plain, (![B_8, A_7]: (~r1_xboole_0(B_8, A_7) | ~r1_tarski(B_8, A_7))), inference(negUnitSimplification, [status(thm)], [c_84, c_10])).
% 2.56/1.44  tff(c_268, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_233, c_116])).
% 2.56/1.44  tff(c_276, plain, (~v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_18, c_268])).
% 2.56/1.44  tff(c_280, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_185, c_276])).
% 2.56/1.44  tff(c_281, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_66])).
% 2.56/1.44  tff(c_367, plain, (![C_112, B_113, A_114]: (v5_relat_1(C_112, B_113) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_114, B_113))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.56/1.44  tff(c_381, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_367])).
% 2.56/1.44  tff(c_446, plain, (![A_127, B_128, C_129]: (k2_relset_1(A_127, B_128, C_129)=k2_relat_1(C_129) | ~m1_subset_1(C_129, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.56/1.44  tff(c_460, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_446])).
% 2.56/1.44  tff(c_323, plain, (![A_98, B_99]: (r2_hidden('#skF_1'(A_98, B_99), B_99) | r1_xboole_0(A_98, B_99))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.56/1.44  tff(c_340, plain, (![A_103, B_104]: (m1_subset_1('#skF_1'(A_103, B_104), B_104) | r1_xboole_0(A_103, B_104))), inference(resolution, [status(thm)], [c_323, c_12])).
% 2.56/1.44  tff(c_305, plain, (![A_92, B_93]: (r2_hidden('#skF_1'(A_92, B_93), A_92) | r1_xboole_0(A_92, B_93))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.56/1.44  tff(c_313, plain, (![B_93]: (~m1_subset_1('#skF_1'(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), B_93), '#skF_3') | r1_xboole_0(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), B_93))), inference(resolution, [status(thm)], [c_305, c_34])).
% 2.56/1.44  tff(c_349, plain, (r1_xboole_0(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_340, c_313])).
% 2.56/1.44  tff(c_354, plain, (~r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), '#skF_3') | v1_xboole_0(k2_relset_1('#skF_2', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_349, c_10])).
% 2.56/1.44  tff(c_430, plain, (~r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_354])).
% 2.56/1.44  tff(c_461, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_460, c_430])).
% 2.56/1.44  tff(c_502, plain, (~v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_18, c_461])).
% 2.56/1.44  tff(c_506, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_322, c_381, c_502])).
% 2.56/1.44  tff(c_507, plain, (v1_xboole_0(k2_relset_1('#skF_2', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_354])).
% 2.56/1.44  tff(c_516, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_507, c_2])).
% 2.56/1.44  tff(c_536, plain, (![A_131, B_132, C_133]: (k2_relset_1(A_131, B_132, C_133)=k2_relat_1(C_133) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.56/1.44  tff(c_547, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_536])).
% 2.56/1.44  tff(c_551, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_516, c_547])).
% 2.56/1.44  tff(c_24, plain, (![A_19]: (~v1_xboole_0(k2_relat_1(A_19)) | ~v1_relat_1(A_19) | v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.56/1.44  tff(c_561, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_551, c_24])).
% 2.56/1.44  tff(c_569, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_322, c_281, c_561])).
% 2.56/1.44  tff(c_49, plain, (![A_44]: (k1_relat_1(A_44)=k1_xboole_0 | ~v1_xboole_0(A_44))), inference(resolution, [status(thm)], [c_45, c_2])).
% 2.56/1.44  tff(c_573, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_569, c_49])).
% 2.56/1.44  tff(c_580, plain, $false, inference(negUnitSimplification, [status(thm)], [c_425, c_573])).
% 2.56/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.44  
% 2.56/1.44  Inference rules
% 2.56/1.44  ----------------------
% 2.56/1.44  #Ref     : 0
% 2.56/1.44  #Sup     : 108
% 2.56/1.44  #Fact    : 0
% 2.56/1.44  #Define  : 0
% 2.56/1.44  #Split   : 2
% 2.56/1.44  #Chain   : 0
% 2.56/1.44  #Close   : 0
% 2.56/1.44  
% 2.56/1.44  Ordering : KBO
% 2.56/1.44  
% 2.56/1.44  Simplification rules
% 2.56/1.44  ----------------------
% 2.56/1.44  #Subsume      : 15
% 2.56/1.44  #Demod        : 51
% 2.56/1.44  #Tautology    : 26
% 2.56/1.44  #SimpNegUnit  : 6
% 2.56/1.44  #BackRed      : 24
% 2.56/1.44  
% 2.56/1.44  #Partial instantiations: 0
% 2.56/1.44  #Strategies tried      : 1
% 2.56/1.44  
% 2.56/1.44  Timing (in seconds)
% 2.56/1.44  ----------------------
% 2.56/1.44  Preprocessing        : 0.31
% 2.56/1.44  Parsing              : 0.17
% 2.56/1.44  CNF conversion       : 0.02
% 2.56/1.44  Main loop            : 0.28
% 2.56/1.44  Inferencing          : 0.11
% 2.56/1.44  Reduction            : 0.08
% 2.56/1.44  Demodulation         : 0.05
% 2.56/1.44  BG Simplification    : 0.02
% 2.56/1.44  Subsumption          : 0.05
% 2.56/1.44  Abstraction          : 0.02
% 2.56/1.44  MUC search           : 0.00
% 2.56/1.44  Cooper               : 0.00
% 2.56/1.44  Total                : 0.63
% 2.56/1.44  Index Insertion      : 0.00
% 2.56/1.44  Index Deletion       : 0.00
% 2.56/1.44  Index Matching       : 0.00
% 2.56/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
