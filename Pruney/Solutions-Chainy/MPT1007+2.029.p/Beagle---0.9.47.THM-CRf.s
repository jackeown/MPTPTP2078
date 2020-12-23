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
% DateTime   : Thu Dec  3 10:14:15 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 2.90s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 162 expanded)
%              Number of leaves         :   47 (  76 expanded)
%              Depth                    :   11
%              Number of atoms          :  142 ( 317 expanded)
%              Number of equality atoms :   27 (  57 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_42,axiom,(
    ! [A,B] : ~ v1_xboole_0(k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_126,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_114,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

tff(c_56,plain,(
    ! [A_52] : k2_tarski(A_52,A_52) = k1_tarski(A_52) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_12,B_13] : ~ v1_xboole_0(k2_tarski(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_61,plain,(
    ! [A_52] : ~ v1_xboole_0(k1_tarski(A_52)) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_14])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_73,plain,(
    ! [B_55,A_56] :
      ( ~ r1_tarski(B_55,A_56)
      | ~ r2_hidden(A_56,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_78,plain,(
    ! [A_57] :
      ( ~ r1_tarski(A_57,'#skF_1'(A_57))
      | v1_xboole_0(A_57) ) ),
    inference(resolution,[status(thm)],[c_4,c_73])).

tff(c_83,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_78])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_93,plain,(
    ! [C_60,A_61,B_62] :
      ( v1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_97,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_93])).

tff(c_122,plain,(
    ! [C_73,A_74,B_75] :
      ( v4_relat_1(C_73,A_74)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_126,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_48,c_122])).

tff(c_26,plain,(
    ! [B_26,A_25] :
      ( k7_relat_1(B_26,A_25) = B_26
      | ~ v4_relat_1(B_26,A_25)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_129,plain,
    ( k7_relat_1('#skF_4',k1_tarski('#skF_2')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_126,c_26])).

tff(c_132,plain,(
    k7_relat_1('#skF_4',k1_tarski('#skF_2')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_129])).

tff(c_137,plain,(
    ! [B_76,A_77] :
      ( k2_relat_1(k7_relat_1(B_76,A_77)) = k9_relat_1(B_76,A_77)
      | ~ v1_relat_1(B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_146,plain,
    ( k9_relat_1('#skF_4',k1_tarski('#skF_2')) = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_137])).

tff(c_150,plain,(
    k9_relat_1('#skF_4',k1_tarski('#skF_2')) = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_146])).

tff(c_18,plain,(
    ! [A_18,B_20] :
      ( k9_relat_1(A_18,k1_tarski(B_20)) = k11_relat_1(A_18,B_20)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_154,plain,
    ( k11_relat_1('#skF_4','#skF_2') = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_18])).

tff(c_161,plain,(
    k11_relat_1('#skF_4','#skF_2') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_154])).

tff(c_22,plain,(
    ! [A_23,B_24] :
      ( r2_hidden(A_23,k1_relat_1(B_24))
      | k11_relat_1(B_24,A_23) = k1_xboole_0
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_52,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_219,plain,(
    ! [A_91,B_92,C_93] :
      ( k2_relset_1(A_91,B_92,C_93) = k2_relat_1(C_93)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_223,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_219])).

tff(c_229,plain,(
    ! [A_94,B_95,C_96] :
      ( m1_subset_1(k2_relset_1(A_94,B_95,C_96),k1_zfmisc_1(B_95))
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_251,plain,
    ( m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_229])).

tff(c_258,plain,(
    m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_251])).

tff(c_271,plain,(
    ! [B_101,A_102] :
      ( r2_hidden(k1_funct_1(B_101,A_102),k2_relat_1(B_101))
      | ~ r2_hidden(A_102,k1_relat_1(B_101))
      | ~ v1_funct_1(B_101)
      | ~ v1_relat_1(B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_16,plain,(
    ! [C_17,A_14,B_15] :
      ( r2_hidden(C_17,A_14)
      | ~ r2_hidden(C_17,B_15)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_517,plain,(
    ! [B_161,A_162,A_163] :
      ( r2_hidden(k1_funct_1(B_161,A_162),A_163)
      | ~ m1_subset_1(k2_relat_1(B_161),k1_zfmisc_1(A_163))
      | ~ r2_hidden(A_162,k1_relat_1(B_161))
      | ~ v1_funct_1(B_161)
      | ~ v1_relat_1(B_161) ) ),
    inference(resolution,[status(thm)],[c_271,c_16])).

tff(c_519,plain,(
    ! [A_162] :
      ( r2_hidden(k1_funct_1('#skF_4',A_162),'#skF_3')
      | ~ r2_hidden(A_162,k1_relat_1('#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_258,c_517])).

tff(c_525,plain,(
    ! [A_164] :
      ( r2_hidden(k1_funct_1('#skF_4',A_164),'#skF_3')
      | ~ r2_hidden(A_164,k1_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_52,c_519])).

tff(c_44,plain,(
    ~ r2_hidden(k1_funct_1('#skF_4','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_540,plain,(
    ~ r2_hidden('#skF_2',k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_525,c_44])).

tff(c_543,plain,
    ( k11_relat_1('#skF_4','#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_540])).

tff(c_546,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_161,c_543])).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_50,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_308,plain,(
    ! [D_107,C_108,A_109,B_110] :
      ( r2_hidden(k1_funct_1(D_107,C_108),k2_relset_1(A_109,B_110,D_107))
      | k1_xboole_0 = B_110
      | ~ r2_hidden(C_108,A_109)
      | ~ m1_subset_1(D_107,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110)))
      | ~ v1_funct_2(D_107,A_109,B_110)
      | ~ v1_funct_1(D_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_319,plain,(
    ! [C_108] :
      ( r2_hidden(k1_funct_1('#skF_4',C_108),k2_relat_1('#skF_4'))
      | k1_xboole_0 = '#skF_3'
      | ~ r2_hidden(C_108,k1_tarski('#skF_2'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3')))
      | ~ v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_308])).

tff(c_324,plain,(
    ! [C_108] :
      ( r2_hidden(k1_funct_1('#skF_4',C_108),k2_relat_1('#skF_4'))
      | k1_xboole_0 = '#skF_3'
      | ~ r2_hidden(C_108,k1_tarski('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_319])).

tff(c_330,plain,(
    ! [C_112] :
      ( r2_hidden(k1_funct_1('#skF_4',C_112),k2_relat_1('#skF_4'))
      | ~ r2_hidden(C_112,k1_tarski('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_324])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_341,plain,(
    ! [C_112] :
      ( ~ v1_xboole_0(k2_relat_1('#skF_4'))
      | ~ r2_hidden(C_112,k1_tarski('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_330,c_2])).

tff(c_342,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_341])).

tff(c_550,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_546,c_342])).

tff(c_560,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_550])).

tff(c_575,plain,(
    ! [C_166] : ~ r2_hidden(C_166,k1_tarski('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_341])).

tff(c_583,plain,(
    v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_4,c_575])).

tff(c_588,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_583])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n017.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 18:44:01 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.75/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.47  
% 2.75/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.47  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.75/1.47  
% 2.75/1.47  %Foreground sorts:
% 2.75/1.47  
% 2.75/1.47  
% 2.75/1.47  %Background operators:
% 2.75/1.47  
% 2.75/1.47  
% 2.75/1.47  %Foreground operators:
% 2.75/1.47  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.75/1.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.75/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.75/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.75/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.75/1.47  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.75/1.47  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.75/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.75/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.75/1.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.75/1.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.75/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.75/1.47  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.75/1.47  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.75/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.75/1.47  tff('#skF_2', type, '#skF_2': $i).
% 2.75/1.47  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.75/1.47  tff('#skF_3', type, '#skF_3': $i).
% 2.75/1.47  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.75/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.75/1.47  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.75/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.75/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.75/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.75/1.47  tff('#skF_4', type, '#skF_4': $i).
% 2.75/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.75/1.47  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.75/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.75/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.75/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.75/1.47  
% 2.90/1.49  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.90/1.49  tff(f_42, axiom, (![A, B]: ~v1_xboole_0(k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_xboole_0)).
% 2.90/1.49  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.90/1.49  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.90/1.49  tff(f_84, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.90/1.49  tff(f_126, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_2)).
% 2.90/1.49  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.90/1.49  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.90/1.49  tff(f_71, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.90/1.49  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.90/1.49  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 2.90/1.49  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 2.90/1.49  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.90/1.49  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 2.90/1.49  tff(f_79, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 2.90/1.49  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 2.90/1.49  tff(f_114, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_funct_2)).
% 2.90/1.49  tff(c_56, plain, (![A_52]: (k2_tarski(A_52, A_52)=k1_tarski(A_52))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.90/1.49  tff(c_14, plain, (![A_12, B_13]: (~v1_xboole_0(k2_tarski(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.90/1.49  tff(c_61, plain, (![A_52]: (~v1_xboole_0(k1_tarski(A_52)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_14])).
% 2.90/1.49  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.90/1.49  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.90/1.49  tff(c_73, plain, (![B_55, A_56]: (~r1_tarski(B_55, A_56) | ~r2_hidden(A_56, B_55))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.90/1.49  tff(c_78, plain, (![A_57]: (~r1_tarski(A_57, '#skF_1'(A_57)) | v1_xboole_0(A_57))), inference(resolution, [status(thm)], [c_4, c_73])).
% 2.90/1.49  tff(c_83, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_78])).
% 2.90/1.49  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.90/1.49  tff(c_93, plain, (![C_60, A_61, B_62]: (v1_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.90/1.49  tff(c_97, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_93])).
% 2.90/1.49  tff(c_122, plain, (![C_73, A_74, B_75]: (v4_relat_1(C_73, A_74) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.90/1.49  tff(c_126, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_48, c_122])).
% 2.90/1.49  tff(c_26, plain, (![B_26, A_25]: (k7_relat_1(B_26, A_25)=B_26 | ~v4_relat_1(B_26, A_25) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.90/1.49  tff(c_129, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_2'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_126, c_26])).
% 2.90/1.49  tff(c_132, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_2'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_97, c_129])).
% 2.90/1.49  tff(c_137, plain, (![B_76, A_77]: (k2_relat_1(k7_relat_1(B_76, A_77))=k9_relat_1(B_76, A_77) | ~v1_relat_1(B_76))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.90/1.49  tff(c_146, plain, (k9_relat_1('#skF_4', k1_tarski('#skF_2'))=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_132, c_137])).
% 2.90/1.49  tff(c_150, plain, (k9_relat_1('#skF_4', k1_tarski('#skF_2'))=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_146])).
% 2.90/1.49  tff(c_18, plain, (![A_18, B_20]: (k9_relat_1(A_18, k1_tarski(B_20))=k11_relat_1(A_18, B_20) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.90/1.49  tff(c_154, plain, (k11_relat_1('#skF_4', '#skF_2')=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_150, c_18])).
% 2.90/1.49  tff(c_161, plain, (k11_relat_1('#skF_4', '#skF_2')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_154])).
% 2.90/1.49  tff(c_22, plain, (![A_23, B_24]: (r2_hidden(A_23, k1_relat_1(B_24)) | k11_relat_1(B_24, A_23)=k1_xboole_0 | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.90/1.49  tff(c_52, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.90/1.49  tff(c_219, plain, (![A_91, B_92, C_93]: (k2_relset_1(A_91, B_92, C_93)=k2_relat_1(C_93) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.90/1.49  tff(c_223, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_219])).
% 2.90/1.49  tff(c_229, plain, (![A_94, B_95, C_96]: (m1_subset_1(k2_relset_1(A_94, B_95, C_96), k1_zfmisc_1(B_95)) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.90/1.49  tff(c_251, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_223, c_229])).
% 2.90/1.49  tff(c_258, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_251])).
% 2.90/1.49  tff(c_271, plain, (![B_101, A_102]: (r2_hidden(k1_funct_1(B_101, A_102), k2_relat_1(B_101)) | ~r2_hidden(A_102, k1_relat_1(B_101)) | ~v1_funct_1(B_101) | ~v1_relat_1(B_101))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.90/1.49  tff(c_16, plain, (![C_17, A_14, B_15]: (r2_hidden(C_17, A_14) | ~r2_hidden(C_17, B_15) | ~m1_subset_1(B_15, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.90/1.49  tff(c_517, plain, (![B_161, A_162, A_163]: (r2_hidden(k1_funct_1(B_161, A_162), A_163) | ~m1_subset_1(k2_relat_1(B_161), k1_zfmisc_1(A_163)) | ~r2_hidden(A_162, k1_relat_1(B_161)) | ~v1_funct_1(B_161) | ~v1_relat_1(B_161))), inference(resolution, [status(thm)], [c_271, c_16])).
% 2.90/1.49  tff(c_519, plain, (![A_162]: (r2_hidden(k1_funct_1('#skF_4', A_162), '#skF_3') | ~r2_hidden(A_162, k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_258, c_517])).
% 2.90/1.49  tff(c_525, plain, (![A_164]: (r2_hidden(k1_funct_1('#skF_4', A_164), '#skF_3') | ~r2_hidden(A_164, k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_52, c_519])).
% 2.90/1.49  tff(c_44, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.90/1.49  tff(c_540, plain, (~r2_hidden('#skF_2', k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_525, c_44])).
% 2.90/1.49  tff(c_543, plain, (k11_relat_1('#skF_4', '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_540])).
% 2.90/1.49  tff(c_546, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_97, c_161, c_543])).
% 2.90/1.49  tff(c_46, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.90/1.49  tff(c_50, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.90/1.49  tff(c_308, plain, (![D_107, C_108, A_109, B_110]: (r2_hidden(k1_funct_1(D_107, C_108), k2_relset_1(A_109, B_110, D_107)) | k1_xboole_0=B_110 | ~r2_hidden(C_108, A_109) | ~m1_subset_1(D_107, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))) | ~v1_funct_2(D_107, A_109, B_110) | ~v1_funct_1(D_107))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.90/1.49  tff(c_319, plain, (![C_108]: (r2_hidden(k1_funct_1('#skF_4', C_108), k2_relat_1('#skF_4')) | k1_xboole_0='#skF_3' | ~r2_hidden(C_108, k1_tarski('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3'))) | ~v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3') | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_223, c_308])).
% 2.90/1.49  tff(c_324, plain, (![C_108]: (r2_hidden(k1_funct_1('#skF_4', C_108), k2_relat_1('#skF_4')) | k1_xboole_0='#skF_3' | ~r2_hidden(C_108, k1_tarski('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_319])).
% 2.90/1.49  tff(c_330, plain, (![C_112]: (r2_hidden(k1_funct_1('#skF_4', C_112), k2_relat_1('#skF_4')) | ~r2_hidden(C_112, k1_tarski('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_46, c_324])).
% 2.90/1.49  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.90/1.49  tff(c_341, plain, (![C_112]: (~v1_xboole_0(k2_relat_1('#skF_4')) | ~r2_hidden(C_112, k1_tarski('#skF_2')))), inference(resolution, [status(thm)], [c_330, c_2])).
% 2.90/1.49  tff(c_342, plain, (~v1_xboole_0(k2_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_341])).
% 2.90/1.49  tff(c_550, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_546, c_342])).
% 2.90/1.49  tff(c_560, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83, c_550])).
% 2.90/1.49  tff(c_575, plain, (![C_166]: (~r2_hidden(C_166, k1_tarski('#skF_2')))), inference(splitRight, [status(thm)], [c_341])).
% 2.90/1.49  tff(c_583, plain, (v1_xboole_0(k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_4, c_575])).
% 2.90/1.49  tff(c_588, plain, $false, inference(negUnitSimplification, [status(thm)], [c_61, c_583])).
% 2.90/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.90/1.49  
% 2.90/1.49  Inference rules
% 2.90/1.49  ----------------------
% 2.90/1.49  #Ref     : 0
% 2.90/1.49  #Sup     : 110
% 2.90/1.49  #Fact    : 0
% 2.90/1.49  #Define  : 0
% 2.90/1.49  #Split   : 6
% 2.90/1.49  #Chain   : 0
% 2.90/1.49  #Close   : 0
% 2.90/1.49  
% 2.90/1.49  Ordering : KBO
% 2.90/1.49  
% 2.90/1.49  Simplification rules
% 2.90/1.49  ----------------------
% 2.90/1.49  #Subsume      : 15
% 2.90/1.49  #Demod        : 28
% 2.90/1.49  #Tautology    : 21
% 2.90/1.49  #SimpNegUnit  : 5
% 2.90/1.49  #BackRed      : 9
% 2.90/1.49  
% 2.90/1.49  #Partial instantiations: 0
% 2.90/1.49  #Strategies tried      : 1
% 2.90/1.49  
% 2.90/1.49  Timing (in seconds)
% 2.90/1.49  ----------------------
% 2.90/1.49  Preprocessing        : 0.34
% 2.90/1.49  Parsing              : 0.19
% 2.90/1.49  CNF conversion       : 0.02
% 2.90/1.49  Main loop            : 0.32
% 2.90/1.49  Inferencing          : 0.12
% 2.90/1.49  Reduction            : 0.09
% 2.90/1.49  Demodulation         : 0.06
% 2.90/1.49  BG Simplification    : 0.02
% 2.90/1.49  Subsumption          : 0.07
% 2.90/1.49  Abstraction          : 0.01
% 2.90/1.49  MUC search           : 0.00
% 2.90/1.49  Cooper               : 0.00
% 2.90/1.49  Total                : 0.70
% 2.90/1.49  Index Insertion      : 0.00
% 2.90/1.49  Index Deletion       : 0.00
% 2.90/1.49  Index Matching       : 0.00
% 2.90/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
