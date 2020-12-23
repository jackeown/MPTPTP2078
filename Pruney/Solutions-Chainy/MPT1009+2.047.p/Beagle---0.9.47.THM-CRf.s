%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:48 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 175 expanded)
%              Number of leaves         :   45 (  82 expanded)
%              Depth                    :   11
%              Number of atoms          :  108 ( 325 expanded)
%              Number of equality atoms :   42 (  80 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_115,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).

tff(f_85,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_62,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_95,plain,(
    ! [C_48,A_49,B_50] :
      ( v1_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_99,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_95])).

tff(c_148,plain,(
    ! [C_68,A_69,B_70] :
      ( v4_relat_1(C_68,A_69)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_152,plain,(
    v4_relat_1('#skF_6',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_62,c_148])).

tff(c_32,plain,(
    ! [B_21,A_20] :
      ( k7_relat_1(B_21,A_20) = B_21
      | ~ v4_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_155,plain,
    ( k7_relat_1('#skF_6',k1_tarski('#skF_3')) = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_152,c_32])).

tff(c_158,plain,(
    k7_relat_1('#skF_6',k1_tarski('#skF_3')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_155])).

tff(c_163,plain,(
    ! [B_71,A_72] :
      ( k2_relat_1(k7_relat_1(B_71,A_72)) = k9_relat_1(B_71,A_72)
      | ~ v1_relat_1(B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_175,plain,
    ( k9_relat_1('#skF_6',k1_tarski('#skF_3')) = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_163])).

tff(c_179,plain,(
    k9_relat_1('#skF_6',k1_tarski('#skF_3')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_175])).

tff(c_28,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k9_relat_1(B_17,A_16),k2_relat_1(B_17))
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_243,plain,(
    ! [B_98,A_99,A_100] :
      ( r1_tarski(k9_relat_1(k7_relat_1(B_98,A_99),A_100),k9_relat_1(B_98,A_99))
      | ~ v1_relat_1(k7_relat_1(B_98,A_99))
      | ~ v1_relat_1(B_98) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_28])).

tff(c_249,plain,(
    ! [A_100] :
      ( r1_tarski(k9_relat_1('#skF_6',A_100),k9_relat_1('#skF_6',k1_tarski('#skF_3')))
      | ~ v1_relat_1(k7_relat_1('#skF_6',k1_tarski('#skF_3')))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_243])).

tff(c_260,plain,(
    ! [A_100] : r1_tarski(k9_relat_1('#skF_6',A_100),k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_99,c_158,c_179,c_249])).

tff(c_66,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_26,plain,(
    ! [A_13,B_15] :
      ( k9_relat_1(A_13,k1_tarski(B_15)) = k11_relat_1(A_13,B_15)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_184,plain,
    ( k11_relat_1('#skF_6','#skF_3') = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_26])).

tff(c_194,plain,(
    k11_relat_1('#skF_6','#skF_3') = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_184])).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_64,plain,(
    v1_funct_2('#skF_6',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_214,plain,(
    ! [A_76,B_77,C_78] :
      ( k1_relset_1(A_76,B_77,C_78) = k1_relat_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_218,plain,(
    k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_214])).

tff(c_277,plain,(
    ! [B_106,A_107,C_108] :
      ( k1_xboole_0 = B_106
      | k1_relset_1(A_107,B_106,C_108) = A_107
      | ~ v1_funct_2(C_108,A_107,B_106)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_107,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_280,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6') = k1_tarski('#skF_3')
    | ~ v1_funct_2('#skF_6',k1_tarski('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_277])).

tff(c_283,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_tarski('#skF_3') = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_218,c_280])).

tff(c_284,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_283])).

tff(c_68,plain,(
    ! [A_42] : k2_tarski(A_42,A_42) = k1_tarski(A_42) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_4,plain,(
    ! [D_6,A_1] : r2_hidden(D_6,k2_tarski(A_1,D_6)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_74,plain,(
    ! [A_42] : r2_hidden(A_42,k1_tarski(A_42)) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_4])).

tff(c_301,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_284,c_74])).

tff(c_34,plain,(
    ! [B_23,A_22] :
      ( k1_tarski(k1_funct_1(B_23,A_22)) = k11_relat_1(B_23,A_22)
      | ~ r2_hidden(A_22,k1_relat_1(B_23))
      | ~ v1_funct_1(B_23)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_313,plain,
    ( k1_tarski(k1_funct_1('#skF_6','#skF_3')) = k11_relat_1('#skF_6','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_301,c_34])).

tff(c_316,plain,(
    k1_tarski(k1_funct_1('#skF_6','#skF_3')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_66,c_194,c_313])).

tff(c_223,plain,(
    ! [A_79,B_80,C_81,D_82] :
      ( k7_relset_1(A_79,B_80,C_81,D_82) = k9_relat_1(C_81,D_82)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_226,plain,(
    ! [D_82] : k7_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6',D_82) = k9_relat_1('#skF_6',D_82) ),
    inference(resolution,[status(thm)],[c_62,c_223])).

tff(c_58,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6','#skF_5'),k1_tarski(k1_funct_1('#skF_6','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_227,plain,(
    ~ r1_tarski(k9_relat_1('#skF_6','#skF_5'),k1_tarski(k1_funct_1('#skF_6','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_58])).

tff(c_351,plain,(
    ~ r1_tarski(k9_relat_1('#skF_6','#skF_5'),k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_227])).

tff(c_354,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_351])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:15:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.47/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.53  
% 2.61/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.54  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 2.61/1.54  
% 2.61/1.54  %Foreground sorts:
% 2.61/1.54  
% 2.61/1.54  
% 2.61/1.54  %Background operators:
% 2.61/1.54  
% 2.61/1.54  
% 2.61/1.54  %Foreground operators:
% 2.61/1.54  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.61/1.54  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.61/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.61/1.54  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.61/1.54  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.61/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.61/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.61/1.54  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.61/1.54  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.61/1.54  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.61/1.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.61/1.54  tff('#skF_5', type, '#skF_5': $i).
% 2.61/1.54  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.61/1.54  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.61/1.54  tff('#skF_6', type, '#skF_6': $i).
% 2.61/1.54  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.61/1.54  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.61/1.54  tff('#skF_3', type, '#skF_3': $i).
% 2.61/1.54  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.61/1.54  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.61/1.54  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.61/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.61/1.54  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.61/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.61/1.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.61/1.54  tff('#skF_4', type, '#skF_4': $i).
% 2.61/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.54  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.61/1.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.61/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.61/1.54  
% 2.61/1.55  tff(f_115, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 2.61/1.55  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.61/1.55  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.61/1.55  tff(f_59, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.61/1.55  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.61/1.55  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 2.61/1.55  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 2.61/1.55  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.61/1.55  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.61/1.55  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.61/1.55  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.61/1.55  tff(f_67, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k11_relat_1(B, A) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_funct_1)).
% 2.61/1.55  tff(f_85, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.61/1.55  tff(c_62, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.61/1.55  tff(c_95, plain, (![C_48, A_49, B_50]: (v1_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.61/1.55  tff(c_99, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_62, c_95])).
% 2.61/1.55  tff(c_148, plain, (![C_68, A_69, B_70]: (v4_relat_1(C_68, A_69) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.61/1.55  tff(c_152, plain, (v4_relat_1('#skF_6', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_62, c_148])).
% 2.61/1.55  tff(c_32, plain, (![B_21, A_20]: (k7_relat_1(B_21, A_20)=B_21 | ~v4_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.61/1.55  tff(c_155, plain, (k7_relat_1('#skF_6', k1_tarski('#skF_3'))='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_152, c_32])).
% 2.61/1.55  tff(c_158, plain, (k7_relat_1('#skF_6', k1_tarski('#skF_3'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_99, c_155])).
% 2.61/1.55  tff(c_163, plain, (![B_71, A_72]: (k2_relat_1(k7_relat_1(B_71, A_72))=k9_relat_1(B_71, A_72) | ~v1_relat_1(B_71))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.61/1.55  tff(c_175, plain, (k9_relat_1('#skF_6', k1_tarski('#skF_3'))=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_158, c_163])).
% 2.61/1.55  tff(c_179, plain, (k9_relat_1('#skF_6', k1_tarski('#skF_3'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_99, c_175])).
% 2.61/1.55  tff(c_28, plain, (![B_17, A_16]: (r1_tarski(k9_relat_1(B_17, A_16), k2_relat_1(B_17)) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.61/1.55  tff(c_243, plain, (![B_98, A_99, A_100]: (r1_tarski(k9_relat_1(k7_relat_1(B_98, A_99), A_100), k9_relat_1(B_98, A_99)) | ~v1_relat_1(k7_relat_1(B_98, A_99)) | ~v1_relat_1(B_98))), inference(superposition, [status(thm), theory('equality')], [c_163, c_28])).
% 2.61/1.55  tff(c_249, plain, (![A_100]: (r1_tarski(k9_relat_1('#skF_6', A_100), k9_relat_1('#skF_6', k1_tarski('#skF_3'))) | ~v1_relat_1(k7_relat_1('#skF_6', k1_tarski('#skF_3'))) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_158, c_243])).
% 2.61/1.55  tff(c_260, plain, (![A_100]: (r1_tarski(k9_relat_1('#skF_6', A_100), k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_99, c_158, c_179, c_249])).
% 2.61/1.55  tff(c_66, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.61/1.55  tff(c_26, plain, (![A_13, B_15]: (k9_relat_1(A_13, k1_tarski(B_15))=k11_relat_1(A_13, B_15) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.61/1.55  tff(c_184, plain, (k11_relat_1('#skF_6', '#skF_3')=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_179, c_26])).
% 2.61/1.55  tff(c_194, plain, (k11_relat_1('#skF_6', '#skF_3')=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_99, c_184])).
% 2.61/1.55  tff(c_60, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.61/1.55  tff(c_64, plain, (v1_funct_2('#skF_6', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.61/1.55  tff(c_214, plain, (![A_76, B_77, C_78]: (k1_relset_1(A_76, B_77, C_78)=k1_relat_1(C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.61/1.55  tff(c_218, plain, (k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_62, c_214])).
% 2.61/1.55  tff(c_277, plain, (![B_106, A_107, C_108]: (k1_xboole_0=B_106 | k1_relset_1(A_107, B_106, C_108)=A_107 | ~v1_funct_2(C_108, A_107, B_106) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_107, B_106))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.61/1.55  tff(c_280, plain, (k1_xboole_0='#skF_4' | k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6')=k1_tarski('#skF_3') | ~v1_funct_2('#skF_6', k1_tarski('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_62, c_277])).
% 2.61/1.55  tff(c_283, plain, (k1_xboole_0='#skF_4' | k1_tarski('#skF_3')=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_218, c_280])).
% 2.61/1.55  tff(c_284, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_60, c_283])).
% 2.61/1.55  tff(c_68, plain, (![A_42]: (k2_tarski(A_42, A_42)=k1_tarski(A_42))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.61/1.55  tff(c_4, plain, (![D_6, A_1]: (r2_hidden(D_6, k2_tarski(A_1, D_6)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.61/1.55  tff(c_74, plain, (![A_42]: (r2_hidden(A_42, k1_tarski(A_42)))), inference(superposition, [status(thm), theory('equality')], [c_68, c_4])).
% 2.61/1.55  tff(c_301, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_284, c_74])).
% 2.61/1.55  tff(c_34, plain, (![B_23, A_22]: (k1_tarski(k1_funct_1(B_23, A_22))=k11_relat_1(B_23, A_22) | ~r2_hidden(A_22, k1_relat_1(B_23)) | ~v1_funct_1(B_23) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.61/1.55  tff(c_313, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_3'))=k11_relat_1('#skF_6', '#skF_3') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_301, c_34])).
% 2.61/1.55  tff(c_316, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_3'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_99, c_66, c_194, c_313])).
% 2.61/1.55  tff(c_223, plain, (![A_79, B_80, C_81, D_82]: (k7_relset_1(A_79, B_80, C_81, D_82)=k9_relat_1(C_81, D_82) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.61/1.55  tff(c_226, plain, (![D_82]: (k7_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6', D_82)=k9_relat_1('#skF_6', D_82))), inference(resolution, [status(thm)], [c_62, c_223])).
% 2.61/1.55  tff(c_58, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6', '#skF_5'), k1_tarski(k1_funct_1('#skF_6', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.61/1.55  tff(c_227, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_5'), k1_tarski(k1_funct_1('#skF_6', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_226, c_58])).
% 2.61/1.55  tff(c_351, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_5'), k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_316, c_227])).
% 2.61/1.55  tff(c_354, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_260, c_351])).
% 2.61/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.55  
% 2.61/1.55  Inference rules
% 2.61/1.55  ----------------------
% 2.61/1.55  #Ref     : 0
% 2.61/1.55  #Sup     : 64
% 2.61/1.55  #Fact    : 0
% 2.61/1.55  #Define  : 0
% 2.61/1.55  #Split   : 0
% 2.61/1.55  #Chain   : 0
% 2.61/1.55  #Close   : 0
% 2.61/1.55  
% 2.61/1.55  Ordering : KBO
% 2.61/1.55  
% 2.61/1.55  Simplification rules
% 2.61/1.55  ----------------------
% 2.61/1.55  #Subsume      : 0
% 2.61/1.55  #Demod        : 52
% 2.61/1.55  #Tautology    : 40
% 2.61/1.55  #SimpNegUnit  : 1
% 2.61/1.55  #BackRed      : 9
% 2.61/1.55  
% 2.61/1.55  #Partial instantiations: 0
% 2.61/1.55  #Strategies tried      : 1
% 2.61/1.55  
% 2.61/1.55  Timing (in seconds)
% 2.61/1.55  ----------------------
% 2.61/1.55  Preprocessing        : 0.43
% 2.61/1.55  Parsing              : 0.22
% 2.61/1.55  CNF conversion       : 0.03
% 2.61/1.56  Main loop            : 0.23
% 2.61/1.56  Inferencing          : 0.08
% 2.61/1.56  Reduction            : 0.08
% 2.61/1.56  Demodulation         : 0.05
% 2.61/1.56  BG Simplification    : 0.02
% 2.61/1.56  Subsumption          : 0.04
% 2.61/1.56  Abstraction          : 0.01
% 2.61/1.56  MUC search           : 0.00
% 2.61/1.56  Cooper               : 0.00
% 2.61/1.56  Total                : 0.69
% 2.61/1.56  Index Insertion      : 0.00
% 2.61/1.56  Index Deletion       : 0.00
% 2.61/1.56  Index Matching       : 0.00
% 2.61/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
