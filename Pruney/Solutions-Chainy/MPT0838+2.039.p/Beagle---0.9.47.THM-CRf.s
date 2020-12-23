%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:14 EST 2020

% Result     : Theorem 2.90s
% Output     : CNFRefutation 2.90s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 164 expanded)
%              Number of leaves         :   41 (  72 expanded)
%              Depth                    :   11
%              Number of atoms          :  142 ( 344 expanded)
%              Number of equality atoms :   32 (  49 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_145,negated_conjecture,(
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

tff(f_120,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_94,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_116,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_124,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_49,axiom,(
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

tff(f_73,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_61,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_110,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_104,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_629,plain,(
    ! [A_138,B_139,C_140] :
      ( k1_relset_1(A_138,B_139,C_140) = k1_relat_1(C_140)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_648,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_629])).

tff(c_50,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_649,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_648,c_50])).

tff(c_30,plain,(
    ! [A_22,B_23] : v1_relat_1(k2_zfmisc_1(A_22,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_82,plain,(
    ! [B_61,A_62] :
      ( v1_relat_1(B_61)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_62))
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_89,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_52,c_82])).

tff(c_93,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_89])).

tff(c_218,plain,(
    ! [C_93,B_94,A_95] :
      ( v5_relat_1(C_93,B_94)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_95,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_237,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_218])).

tff(c_28,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k2_relat_1(B_21),A_20)
      | ~ v5_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_549,plain,(
    ! [A_135,B_136,C_137] :
      ( k2_relset_1(A_135,B_136,C_137) = k2_relat_1(C_137)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_135,B_136))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_568,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_549])).

tff(c_99,plain,(
    ! [A_65,B_66] :
      ( r2_hidden('#skF_2'(A_65,B_66),B_66)
      | r1_xboole_0(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,B_14)
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_110,plain,(
    ! [A_65,B_66] :
      ( m1_subset_1('#skF_2'(A_65,B_66),B_66)
      | r1_xboole_0(A_65,B_66) ) ),
    inference(resolution,[status(thm)],[c_99,c_18])).

tff(c_127,plain,(
    ! [A_72,B_73] :
      ( r2_hidden('#skF_2'(A_72,B_73),A_72)
      | r1_xboole_0(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_48,plain,(
    ! [D_50] :
      ( ~ r2_hidden(D_50,k2_relset_1('#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(D_50,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_169,plain,(
    ! [B_84] :
      ( ~ m1_subset_1('#skF_2'(k2_relset_1('#skF_3','#skF_4','#skF_5'),B_84),'#skF_4')
      | r1_xboole_0(k2_relset_1('#skF_3','#skF_4','#skF_5'),B_84) ) ),
    inference(resolution,[status(thm)],[c_127,c_48])).

tff(c_174,plain,(
    r1_xboole_0(k2_relset_1('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_110,c_169])).

tff(c_16,plain,(
    ! [B_12,A_11] :
      ( ~ r1_xboole_0(B_12,A_11)
      | ~ r1_tarski(B_12,A_11)
      | v1_xboole_0(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_178,plain,
    ( ~ r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0(k2_relset_1('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_174,c_16])).

tff(c_423,plain,(
    ~ r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_178])).

tff(c_569,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_568,c_423])).

tff(c_600,plain,
    ( ~ v5_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_569])).

tff(c_604,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_237,c_600])).

tff(c_605,plain,(
    v1_xboole_0(k2_relset_1('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_114,plain,(
    ! [B_67,A_68] :
      ( ~ v1_xboole_0(B_67)
      | r1_xboole_0(A_68,B_67) ) ),
    inference(resolution,[status(thm)],[c_99,c_2])).

tff(c_14,plain,(
    ! [A_10] :
      ( ~ r1_xboole_0(A_10,A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_123,plain,(
    ! [B_67] :
      ( k1_xboole_0 = B_67
      | ~ v1_xboole_0(B_67) ) ),
    inference(resolution,[status(thm)],[c_114,c_14])).

tff(c_610,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_605,c_123])).

tff(c_708,plain,(
    ! [A_147,B_148,C_149] :
      ( k2_relset_1(A_147,B_148,C_149) = k2_relat_1(C_149)
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(A_147,B_148))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_723,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_708])).

tff(c_728,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_610,c_723])).

tff(c_304,plain,(
    ! [C_101,A_102,B_103] :
      ( v4_relat_1(C_101,A_102)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_323,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_304])).

tff(c_38,plain,(
    ! [B_29,A_28] :
      ( k7_relat_1(B_29,A_28) = B_29
      | ~ v4_relat_1(B_29,A_28)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_326,plain,
    ( k7_relat_1('#skF_5','#skF_3') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_323,c_38])).

tff(c_329,plain,(
    k7_relat_1('#skF_5','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_326])).

tff(c_362,plain,(
    ! [B_110,A_111] :
      ( k2_relat_1(k7_relat_1(B_110,A_111)) = k9_relat_1(B_110,A_111)
      | ~ v1_relat_1(B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_380,plain,
    ( k9_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_329,c_362])).

tff(c_384,plain,(
    k9_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_380])).

tff(c_729,plain,(
    k9_relat_1('#skF_5','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_728,c_384])).

tff(c_24,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k1_relat_1(B_19),A_18)
      | ~ v4_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_389,plain,(
    ! [B_112,A_113] :
      ( r1_xboole_0(k1_relat_1(B_112),A_113)
      | k9_relat_1(B_112,A_113) != k1_xboole_0
      | ~ v1_relat_1(B_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_817,plain,(
    ! [B_162,A_163] :
      ( ~ r1_tarski(k1_relat_1(B_162),A_163)
      | v1_xboole_0(k1_relat_1(B_162))
      | k9_relat_1(B_162,A_163) != k1_xboole_0
      | ~ v1_relat_1(B_162) ) ),
    inference(resolution,[status(thm)],[c_389,c_16])).

tff(c_887,plain,(
    ! [B_173,A_174] :
      ( v1_xboole_0(k1_relat_1(B_173))
      | k9_relat_1(B_173,A_174) != k1_xboole_0
      | ~ v4_relat_1(B_173,A_174)
      | ~ v1_relat_1(B_173) ) ),
    inference(resolution,[status(thm)],[c_24,c_817])).

tff(c_889,plain,
    ( v1_xboole_0(k1_relat_1('#skF_5'))
    | k9_relat_1('#skF_5','#skF_3') != k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_323,c_887])).

tff(c_892,plain,(
    v1_xboole_0(k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_729,c_889])).

tff(c_900,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_892,c_123])).

tff(c_908,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_649,c_900])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:50:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.90/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.90/1.44  
% 2.90/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.90/1.44  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 2.90/1.44  
% 2.90/1.44  %Foreground sorts:
% 2.90/1.44  
% 2.90/1.44  
% 2.90/1.44  %Background operators:
% 2.90/1.44  
% 2.90/1.44  
% 2.90/1.44  %Foreground operators:
% 2.90/1.44  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.90/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.90/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.90/1.44  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.90/1.44  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.90/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.90/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.90/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.90/1.44  tff('#skF_5', type, '#skF_5': $i).
% 2.90/1.44  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.90/1.44  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.90/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.90/1.44  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.90/1.44  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.90/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.90/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.90/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.90/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.90/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.90/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.90/1.45  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.90/1.45  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.90/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.90/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.90/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.90/1.45  
% 2.90/1.46  tff(f_145, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_relset_1)).
% 2.90/1.46  tff(f_120, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.90/1.46  tff(f_94, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.90/1.46  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.90/1.46  tff(f_116, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.90/1.46  tff(f_92, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.90/1.46  tff(f_124, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.90/1.46  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.90/1.46  tff(f_73, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 2.90/1.46  tff(f_69, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.90/1.46  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.90/1.46  tff(f_61, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.90/1.46  tff(f_110, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.90/1.46  tff(f_98, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.90/1.46  tff(f_86, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.90/1.46  tff(f_104, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 2.90/1.46  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_145])).
% 2.90/1.46  tff(c_629, plain, (![A_138, B_139, C_140]: (k1_relset_1(A_138, B_139, C_140)=k1_relat_1(C_140) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.90/1.46  tff(c_648, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_629])).
% 2.90/1.46  tff(c_50, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_145])).
% 2.90/1.46  tff(c_649, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_648, c_50])).
% 2.90/1.46  tff(c_30, plain, (![A_22, B_23]: (v1_relat_1(k2_zfmisc_1(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.90/1.46  tff(c_82, plain, (![B_61, A_62]: (v1_relat_1(B_61) | ~m1_subset_1(B_61, k1_zfmisc_1(A_62)) | ~v1_relat_1(A_62))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.90/1.46  tff(c_89, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_52, c_82])).
% 2.90/1.46  tff(c_93, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_89])).
% 2.90/1.46  tff(c_218, plain, (![C_93, B_94, A_95]: (v5_relat_1(C_93, B_94) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_95, B_94))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.90/1.46  tff(c_237, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_218])).
% 2.90/1.46  tff(c_28, plain, (![B_21, A_20]: (r1_tarski(k2_relat_1(B_21), A_20) | ~v5_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.90/1.46  tff(c_549, plain, (![A_135, B_136, C_137]: (k2_relset_1(A_135, B_136, C_137)=k2_relat_1(C_137) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_135, B_136))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.90/1.46  tff(c_568, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_549])).
% 2.90/1.46  tff(c_99, plain, (![A_65, B_66]: (r2_hidden('#skF_2'(A_65, B_66), B_66) | r1_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.90/1.46  tff(c_18, plain, (![A_13, B_14]: (m1_subset_1(A_13, B_14) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.90/1.46  tff(c_110, plain, (![A_65, B_66]: (m1_subset_1('#skF_2'(A_65, B_66), B_66) | r1_xboole_0(A_65, B_66))), inference(resolution, [status(thm)], [c_99, c_18])).
% 2.90/1.46  tff(c_127, plain, (![A_72, B_73]: (r2_hidden('#skF_2'(A_72, B_73), A_72) | r1_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.90/1.46  tff(c_48, plain, (![D_50]: (~r2_hidden(D_50, k2_relset_1('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(D_50, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_145])).
% 2.90/1.46  tff(c_169, plain, (![B_84]: (~m1_subset_1('#skF_2'(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), B_84), '#skF_4') | r1_xboole_0(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), B_84))), inference(resolution, [status(thm)], [c_127, c_48])).
% 2.90/1.46  tff(c_174, plain, (r1_xboole_0(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_110, c_169])).
% 2.90/1.46  tff(c_16, plain, (![B_12, A_11]: (~r1_xboole_0(B_12, A_11) | ~r1_tarski(B_12, A_11) | v1_xboole_0(B_12))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.90/1.46  tff(c_178, plain, (~r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0(k2_relset_1('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_174, c_16])).
% 2.90/1.46  tff(c_423, plain, (~r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_178])).
% 2.90/1.46  tff(c_569, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_568, c_423])).
% 2.90/1.46  tff(c_600, plain, (~v5_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_28, c_569])).
% 2.90/1.46  tff(c_604, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_93, c_237, c_600])).
% 2.90/1.46  tff(c_605, plain, (v1_xboole_0(k2_relset_1('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_178])).
% 2.90/1.46  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.90/1.46  tff(c_114, plain, (![B_67, A_68]: (~v1_xboole_0(B_67) | r1_xboole_0(A_68, B_67))), inference(resolution, [status(thm)], [c_99, c_2])).
% 2.90/1.46  tff(c_14, plain, (![A_10]: (~r1_xboole_0(A_10, A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.90/1.46  tff(c_123, plain, (![B_67]: (k1_xboole_0=B_67 | ~v1_xboole_0(B_67))), inference(resolution, [status(thm)], [c_114, c_14])).
% 2.90/1.46  tff(c_610, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_605, c_123])).
% 2.90/1.46  tff(c_708, plain, (![A_147, B_148, C_149]: (k2_relset_1(A_147, B_148, C_149)=k2_relat_1(C_149) | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(A_147, B_148))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.90/1.46  tff(c_723, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_708])).
% 2.90/1.46  tff(c_728, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_610, c_723])).
% 2.90/1.46  tff(c_304, plain, (![C_101, A_102, B_103]: (v4_relat_1(C_101, A_102) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.90/1.46  tff(c_323, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_304])).
% 2.90/1.46  tff(c_38, plain, (![B_29, A_28]: (k7_relat_1(B_29, A_28)=B_29 | ~v4_relat_1(B_29, A_28) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.90/1.46  tff(c_326, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_323, c_38])).
% 2.90/1.46  tff(c_329, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_93, c_326])).
% 2.90/1.46  tff(c_362, plain, (![B_110, A_111]: (k2_relat_1(k7_relat_1(B_110, A_111))=k9_relat_1(B_110, A_111) | ~v1_relat_1(B_110))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.90/1.46  tff(c_380, plain, (k9_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_329, c_362])).
% 2.90/1.46  tff(c_384, plain, (k9_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_380])).
% 2.90/1.46  tff(c_729, plain, (k9_relat_1('#skF_5', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_728, c_384])).
% 2.90/1.46  tff(c_24, plain, (![B_19, A_18]: (r1_tarski(k1_relat_1(B_19), A_18) | ~v4_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.90/1.46  tff(c_389, plain, (![B_112, A_113]: (r1_xboole_0(k1_relat_1(B_112), A_113) | k9_relat_1(B_112, A_113)!=k1_xboole_0 | ~v1_relat_1(B_112))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.90/1.46  tff(c_817, plain, (![B_162, A_163]: (~r1_tarski(k1_relat_1(B_162), A_163) | v1_xboole_0(k1_relat_1(B_162)) | k9_relat_1(B_162, A_163)!=k1_xboole_0 | ~v1_relat_1(B_162))), inference(resolution, [status(thm)], [c_389, c_16])).
% 2.90/1.46  tff(c_887, plain, (![B_173, A_174]: (v1_xboole_0(k1_relat_1(B_173)) | k9_relat_1(B_173, A_174)!=k1_xboole_0 | ~v4_relat_1(B_173, A_174) | ~v1_relat_1(B_173))), inference(resolution, [status(thm)], [c_24, c_817])).
% 2.90/1.46  tff(c_889, plain, (v1_xboole_0(k1_relat_1('#skF_5')) | k9_relat_1('#skF_5', '#skF_3')!=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_323, c_887])).
% 2.90/1.46  tff(c_892, plain, (v1_xboole_0(k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_729, c_889])).
% 2.90/1.46  tff(c_900, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_892, c_123])).
% 2.90/1.46  tff(c_908, plain, $false, inference(negUnitSimplification, [status(thm)], [c_649, c_900])).
% 2.90/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.90/1.46  
% 2.90/1.46  Inference rules
% 2.90/1.46  ----------------------
% 2.90/1.46  #Ref     : 0
% 2.90/1.46  #Sup     : 178
% 2.90/1.46  #Fact    : 0
% 2.90/1.46  #Define  : 0
% 2.90/1.46  #Split   : 3
% 2.90/1.46  #Chain   : 0
% 2.90/1.46  #Close   : 0
% 2.90/1.46  
% 2.90/1.46  Ordering : KBO
% 2.90/1.46  
% 2.90/1.46  Simplification rules
% 2.90/1.46  ----------------------
% 2.90/1.46  #Subsume      : 15
% 2.90/1.46  #Demod        : 69
% 2.90/1.46  #Tautology    : 65
% 2.90/1.46  #SimpNegUnit  : 5
% 2.90/1.46  #BackRed      : 21
% 2.90/1.46  
% 2.90/1.46  #Partial instantiations: 0
% 2.90/1.46  #Strategies tried      : 1
% 2.90/1.46  
% 2.90/1.46  Timing (in seconds)
% 2.90/1.46  ----------------------
% 3.28/1.46  Preprocessing        : 0.33
% 3.28/1.46  Parsing              : 0.18
% 3.28/1.47  CNF conversion       : 0.02
% 3.28/1.47  Main loop            : 0.37
% 3.28/1.47  Inferencing          : 0.14
% 3.28/1.47  Reduction            : 0.11
% 3.28/1.47  Demodulation         : 0.08
% 3.28/1.47  BG Simplification    : 0.02
% 3.28/1.47  Subsumption          : 0.06
% 3.28/1.47  Abstraction          : 0.02
% 3.28/1.47  MUC search           : 0.00
% 3.28/1.47  Cooper               : 0.00
% 3.28/1.47  Total                : 0.73
% 3.28/1.47  Index Insertion      : 0.00
% 3.28/1.47  Index Deletion       : 0.00
% 3.28/1.47  Index Matching       : 0.00
% 3.28/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
