%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:13 EST 2020

% Result     : Theorem 3.30s
% Output     : CNFRefutation 3.30s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 159 expanded)
%              Number of leaves         :   42 (  71 expanded)
%              Depth                    :   11
%              Number of atoms          :  138 ( 320 expanded)
%              Number of equality atoms :   31 (  47 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

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

tff(f_147,negated_conjecture,(
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

tff(f_122,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_96,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_118,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_126,axiom,(
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

tff(f_75,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_57,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_112,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_106,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

tff(c_56,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_629,plain,(
    ! [A_139,B_140,C_141] :
      ( k1_relset_1(A_139,B_140,C_141) = k1_relat_1(C_141)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_653,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_629])).

tff(c_54,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_658,plain,(
    k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_653,c_54])).

tff(c_34,plain,(
    ! [A_25,B_26] : v1_relat_1(k2_zfmisc_1(A_25,B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_136,plain,(
    ! [B_77,A_78] :
      ( v1_relat_1(B_77)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(A_78))
      | ~ v1_relat_1(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_147,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_56,c_136])).

tff(c_152,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_147])).

tff(c_279,plain,(
    ! [C_104,B_105,A_106] :
      ( v5_relat_1(C_104,B_105)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_106,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_303,plain,(
    v5_relat_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_279])).

tff(c_32,plain,(
    ! [B_24,A_23] :
      ( r1_tarski(k2_relat_1(B_24),A_23)
      | ~ v5_relat_1(B_24,A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_467,plain,(
    ! [A_133,B_134,C_135] :
      ( k2_relset_1(A_133,B_134,C_135) = k2_relat_1(C_135)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_491,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_467])).

tff(c_98,plain,(
    ! [A_67,B_68] :
      ( r2_hidden('#skF_2'(A_67,B_68),B_68)
      | r1_xboole_0(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_22,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(A_16,B_17)
      | ~ r2_hidden(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_109,plain,(
    ! [A_67,B_68] :
      ( m1_subset_1('#skF_2'(A_67,B_68),B_68)
      | r1_xboole_0(A_67,B_68) ) ),
    inference(resolution,[status(thm)],[c_98,c_22])).

tff(c_120,plain,(
    ! [A_73,B_74] :
      ( r2_hidden('#skF_2'(A_73,B_74),A_73)
      | r1_xboole_0(A_73,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_52,plain,(
    ! [D_53] :
      ( ~ r2_hidden(D_53,k2_relset_1('#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1(D_53,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_345,plain,(
    ! [B_113] :
      ( ~ m1_subset_1('#skF_2'(k2_relset_1('#skF_4','#skF_5','#skF_6'),B_113),'#skF_5')
      | r1_xboole_0(k2_relset_1('#skF_4','#skF_5','#skF_6'),B_113) ) ),
    inference(resolution,[status(thm)],[c_120,c_52])).

tff(c_350,plain,(
    r1_xboole_0(k2_relset_1('#skF_4','#skF_5','#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_109,c_345])).

tff(c_20,plain,(
    ! [B_15,A_14] :
      ( ~ r1_xboole_0(B_15,A_14)
      | ~ r1_tarski(B_15,A_14)
      | v1_xboole_0(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_357,plain,
    ( ~ r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),'#skF_5')
    | v1_xboole_0(k2_relset_1('#skF_4','#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_350,c_20])).

tff(c_426,plain,(
    ~ r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_357])).

tff(c_492,plain,(
    ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_491,c_426])).

tff(c_524,plain,
    ( ~ v5_relat_1('#skF_6','#skF_5')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_32,c_492])).

tff(c_528,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_303,c_524])).

tff(c_529,plain,(
    v1_xboole_0(k2_relset_1('#skF_4','#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_357])).

tff(c_65,plain,(
    ! [A_59] :
      ( r2_hidden('#skF_3'(A_59),A_59)
      | k1_xboole_0 = A_59 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_69,plain,(
    ! [A_59] :
      ( ~ v1_xboole_0(A_59)
      | k1_xboole_0 = A_59 ) ),
    inference(resolution,[status(thm)],[c_65,c_2])).

tff(c_538,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_529,c_69])).

tff(c_562,plain,(
    ! [A_136,B_137,C_138] :
      ( k2_relset_1(A_136,B_137,C_138) = k2_relat_1(C_138)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_581,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_562])).

tff(c_587,plain,(
    k2_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_538,c_581])).

tff(c_209,plain,(
    ! [C_95,A_96,B_97] :
      ( v4_relat_1(C_95,A_96)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_233,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_209])).

tff(c_42,plain,(
    ! [B_32,A_31] :
      ( k7_relat_1(B_32,A_31) = B_32
      | ~ v4_relat_1(B_32,A_31)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_248,plain,
    ( k7_relat_1('#skF_6','#skF_4') = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_233,c_42])).

tff(c_251,plain,(
    k7_relat_1('#skF_6','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_248])).

tff(c_304,plain,(
    ! [B_107,A_108] :
      ( k2_relat_1(k7_relat_1(B_107,A_108)) = k9_relat_1(B_107,A_108)
      | ~ v1_relat_1(B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_322,plain,
    ( k9_relat_1('#skF_6','#skF_4') = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_304])).

tff(c_329,plain,(
    k9_relat_1('#skF_6','#skF_4') = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_322])).

tff(c_605,plain,(
    k9_relat_1('#skF_6','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_587,c_329])).

tff(c_28,plain,(
    ! [B_22,A_21] :
      ( r1_tarski(k1_relat_1(B_22),A_21)
      | ~ v4_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_391,plain,(
    ! [B_118,A_119] :
      ( r1_xboole_0(k1_relat_1(B_118),A_119)
      | k9_relat_1(B_118,A_119) != k1_xboole_0
      | ~ v1_relat_1(B_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_932,plain,(
    ! [B_179,A_180] :
      ( ~ r1_tarski(k1_relat_1(B_179),A_180)
      | v1_xboole_0(k1_relat_1(B_179))
      | k9_relat_1(B_179,A_180) != k1_xboole_0
      | ~ v1_relat_1(B_179) ) ),
    inference(resolution,[status(thm)],[c_391,c_20])).

tff(c_951,plain,(
    ! [B_182,A_183] :
      ( v1_xboole_0(k1_relat_1(B_182))
      | k9_relat_1(B_182,A_183) != k1_xboole_0
      | ~ v4_relat_1(B_182,A_183)
      | ~ v1_relat_1(B_182) ) ),
    inference(resolution,[status(thm)],[c_28,c_932])).

tff(c_957,plain,
    ( v1_xboole_0(k1_relat_1('#skF_6'))
    | k9_relat_1('#skF_6','#skF_4') != k1_xboole_0
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_233,c_951])).

tff(c_964,plain,(
    v1_xboole_0(k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_605,c_957])).

tff(c_973,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_964,c_69])).

tff(c_981,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_658,c_973])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:31:35 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.30/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.30/1.57  
% 3.30/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.30/1.58  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2
% 3.30/1.58  
% 3.30/1.58  %Foreground sorts:
% 3.30/1.58  
% 3.30/1.58  
% 3.30/1.58  %Background operators:
% 3.30/1.58  
% 3.30/1.58  
% 3.30/1.58  %Foreground operators:
% 3.30/1.58  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.30/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.30/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.30/1.58  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.30/1.58  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.30/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.30/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.30/1.58  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.30/1.58  tff('#skF_5', type, '#skF_5': $i).
% 3.30/1.58  tff('#skF_6', type, '#skF_6': $i).
% 3.30/1.58  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.30/1.58  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.30/1.58  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.30/1.58  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.30/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.30/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.30/1.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.30/1.58  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.30/1.58  tff('#skF_4', type, '#skF_4': $i).
% 3.30/1.58  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.30/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.30/1.58  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.30/1.58  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.30/1.58  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.30/1.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.30/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.30/1.58  
% 3.30/1.59  tff(f_147, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_relset_1)).
% 3.30/1.59  tff(f_122, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.30/1.59  tff(f_96, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.30/1.59  tff(f_82, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.30/1.59  tff(f_118, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.30/1.59  tff(f_94, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.30/1.59  tff(f_126, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.30/1.59  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.30/1.59  tff(f_75, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 3.30/1.59  tff(f_71, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 3.30/1.59  tff(f_57, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.30/1.59  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.30/1.59  tff(f_112, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.30/1.59  tff(f_100, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.30/1.59  tff(f_88, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.30/1.59  tff(f_106, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 3.30/1.59  tff(c_56, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.30/1.59  tff(c_629, plain, (![A_139, B_140, C_141]: (k1_relset_1(A_139, B_140, C_141)=k1_relat_1(C_141) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.30/1.59  tff(c_653, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_56, c_629])).
% 3.30/1.59  tff(c_54, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.30/1.59  tff(c_658, plain, (k1_relat_1('#skF_6')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_653, c_54])).
% 3.30/1.59  tff(c_34, plain, (![A_25, B_26]: (v1_relat_1(k2_zfmisc_1(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.30/1.59  tff(c_136, plain, (![B_77, A_78]: (v1_relat_1(B_77) | ~m1_subset_1(B_77, k1_zfmisc_1(A_78)) | ~v1_relat_1(A_78))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.30/1.59  tff(c_147, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_56, c_136])).
% 3.30/1.59  tff(c_152, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_147])).
% 3.30/1.59  tff(c_279, plain, (![C_104, B_105, A_106]: (v5_relat_1(C_104, B_105) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_106, B_105))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.30/1.59  tff(c_303, plain, (v5_relat_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_56, c_279])).
% 3.30/1.59  tff(c_32, plain, (![B_24, A_23]: (r1_tarski(k2_relat_1(B_24), A_23) | ~v5_relat_1(B_24, A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.30/1.59  tff(c_467, plain, (![A_133, B_134, C_135]: (k2_relset_1(A_133, B_134, C_135)=k2_relat_1(C_135) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.30/1.59  tff(c_491, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_56, c_467])).
% 3.30/1.59  tff(c_98, plain, (![A_67, B_68]: (r2_hidden('#skF_2'(A_67, B_68), B_68) | r1_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.30/1.59  tff(c_22, plain, (![A_16, B_17]: (m1_subset_1(A_16, B_17) | ~r2_hidden(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.30/1.59  tff(c_109, plain, (![A_67, B_68]: (m1_subset_1('#skF_2'(A_67, B_68), B_68) | r1_xboole_0(A_67, B_68))), inference(resolution, [status(thm)], [c_98, c_22])).
% 3.30/1.59  tff(c_120, plain, (![A_73, B_74]: (r2_hidden('#skF_2'(A_73, B_74), A_73) | r1_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.30/1.59  tff(c_52, plain, (![D_53]: (~r2_hidden(D_53, k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1(D_53, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.30/1.59  tff(c_345, plain, (![B_113]: (~m1_subset_1('#skF_2'(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), B_113), '#skF_5') | r1_xboole_0(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), B_113))), inference(resolution, [status(thm)], [c_120, c_52])).
% 3.30/1.59  tff(c_350, plain, (r1_xboole_0(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_109, c_345])).
% 3.30/1.59  tff(c_20, plain, (![B_15, A_14]: (~r1_xboole_0(B_15, A_14) | ~r1_tarski(B_15, A_14) | v1_xboole_0(B_15))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.30/1.59  tff(c_357, plain, (~r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), '#skF_5') | v1_xboole_0(k2_relset_1('#skF_4', '#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_350, c_20])).
% 3.30/1.59  tff(c_426, plain, (~r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), '#skF_5')), inference(splitLeft, [status(thm)], [c_357])).
% 3.30/1.59  tff(c_492, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_491, c_426])).
% 3.30/1.59  tff(c_524, plain, (~v5_relat_1('#skF_6', '#skF_5') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_32, c_492])).
% 3.30/1.59  tff(c_528, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_152, c_303, c_524])).
% 3.30/1.59  tff(c_529, plain, (v1_xboole_0(k2_relset_1('#skF_4', '#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_357])).
% 3.30/1.59  tff(c_65, plain, (![A_59]: (r2_hidden('#skF_3'(A_59), A_59) | k1_xboole_0=A_59)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.30/1.59  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.30/1.59  tff(c_69, plain, (![A_59]: (~v1_xboole_0(A_59) | k1_xboole_0=A_59)), inference(resolution, [status(thm)], [c_65, c_2])).
% 3.30/1.59  tff(c_538, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_529, c_69])).
% 3.30/1.59  tff(c_562, plain, (![A_136, B_137, C_138]: (k2_relset_1(A_136, B_137, C_138)=k2_relat_1(C_138) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.30/1.59  tff(c_581, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_56, c_562])).
% 3.30/1.59  tff(c_587, plain, (k2_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_538, c_581])).
% 3.30/1.59  tff(c_209, plain, (![C_95, A_96, B_97]: (v4_relat_1(C_95, A_96) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.30/1.59  tff(c_233, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_56, c_209])).
% 3.30/1.59  tff(c_42, plain, (![B_32, A_31]: (k7_relat_1(B_32, A_31)=B_32 | ~v4_relat_1(B_32, A_31) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.30/1.59  tff(c_248, plain, (k7_relat_1('#skF_6', '#skF_4')='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_233, c_42])).
% 3.30/1.59  tff(c_251, plain, (k7_relat_1('#skF_6', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_152, c_248])).
% 3.30/1.59  tff(c_304, plain, (![B_107, A_108]: (k2_relat_1(k7_relat_1(B_107, A_108))=k9_relat_1(B_107, A_108) | ~v1_relat_1(B_107))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.30/1.59  tff(c_322, plain, (k9_relat_1('#skF_6', '#skF_4')=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_251, c_304])).
% 3.30/1.59  tff(c_329, plain, (k9_relat_1('#skF_6', '#skF_4')=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_152, c_322])).
% 3.30/1.59  tff(c_605, plain, (k9_relat_1('#skF_6', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_587, c_329])).
% 3.30/1.59  tff(c_28, plain, (![B_22, A_21]: (r1_tarski(k1_relat_1(B_22), A_21) | ~v4_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.30/1.59  tff(c_391, plain, (![B_118, A_119]: (r1_xboole_0(k1_relat_1(B_118), A_119) | k9_relat_1(B_118, A_119)!=k1_xboole_0 | ~v1_relat_1(B_118))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.30/1.59  tff(c_932, plain, (![B_179, A_180]: (~r1_tarski(k1_relat_1(B_179), A_180) | v1_xboole_0(k1_relat_1(B_179)) | k9_relat_1(B_179, A_180)!=k1_xboole_0 | ~v1_relat_1(B_179))), inference(resolution, [status(thm)], [c_391, c_20])).
% 3.30/1.59  tff(c_951, plain, (![B_182, A_183]: (v1_xboole_0(k1_relat_1(B_182)) | k9_relat_1(B_182, A_183)!=k1_xboole_0 | ~v4_relat_1(B_182, A_183) | ~v1_relat_1(B_182))), inference(resolution, [status(thm)], [c_28, c_932])).
% 3.30/1.59  tff(c_957, plain, (v1_xboole_0(k1_relat_1('#skF_6')) | k9_relat_1('#skF_6', '#skF_4')!=k1_xboole_0 | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_233, c_951])).
% 3.30/1.59  tff(c_964, plain, (v1_xboole_0(k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_605, c_957])).
% 3.30/1.59  tff(c_973, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_964, c_69])).
% 3.30/1.59  tff(c_981, plain, $false, inference(negUnitSimplification, [status(thm)], [c_658, c_973])).
% 3.30/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.30/1.59  
% 3.30/1.59  Inference rules
% 3.30/1.59  ----------------------
% 3.30/1.59  #Ref     : 0
% 3.30/1.59  #Sup     : 191
% 3.30/1.59  #Fact    : 0
% 3.30/1.59  #Define  : 0
% 3.30/1.59  #Split   : 3
% 3.30/1.59  #Chain   : 0
% 3.30/1.59  #Close   : 0
% 3.30/1.59  
% 3.30/1.59  Ordering : KBO
% 3.30/1.59  
% 3.30/1.59  Simplification rules
% 3.30/1.59  ----------------------
% 3.30/1.59  #Subsume      : 21
% 3.30/1.59  #Demod        : 90
% 3.30/1.59  #Tautology    : 60
% 3.30/1.59  #SimpNegUnit  : 4
% 3.30/1.59  #BackRed      : 22
% 3.30/1.59  
% 3.30/1.59  #Partial instantiations: 0
% 3.30/1.59  #Strategies tried      : 1
% 3.30/1.59  
% 3.30/1.59  Timing (in seconds)
% 3.30/1.59  ----------------------
% 3.30/1.60  Preprocessing        : 0.35
% 3.30/1.60  Parsing              : 0.18
% 3.30/1.60  CNF conversion       : 0.03
% 3.30/1.60  Main loop            : 0.46
% 3.30/1.60  Inferencing          : 0.18
% 3.30/1.60  Reduction            : 0.13
% 3.30/1.60  Demodulation         : 0.09
% 3.30/1.60  BG Simplification    : 0.02
% 3.30/1.60  Subsumption          : 0.08
% 3.30/1.60  Abstraction          : 0.02
% 3.30/1.60  MUC search           : 0.00
% 3.30/1.60  Cooper               : 0.00
% 3.30/1.60  Total                : 0.85
% 3.30/1.60  Index Insertion      : 0.00
% 3.30/1.60  Index Deletion       : 0.00
% 3.30/1.60  Index Matching       : 0.00
% 3.30/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
