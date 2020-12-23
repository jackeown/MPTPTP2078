%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:14 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 104 expanded)
%              Number of leaves         :   39 (  54 expanded)
%              Depth                    :    9
%              Number of atoms          :  104 ( 195 expanded)
%              Number of equality atoms :   33 (  64 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_123,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_112,axiom,(
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

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_38,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_78,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_60,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_62,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_64,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_124,plain,(
    ! [C_55,A_56,B_57] :
      ( v1_relat_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_128,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_124])).

tff(c_68,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_66,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_182,plain,(
    ! [A_79,B_80,C_81] :
      ( k1_relset_1(A_79,B_80,C_81) = k1_relat_1(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_186,plain,(
    k1_relset_1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_182])).

tff(c_309,plain,(
    ! [B_122,A_123,C_124] :
      ( k1_xboole_0 = B_122
      | k1_relset_1(A_123,B_122,C_124) = A_123
      | ~ v1_funct_2(C_124,A_123,B_122)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_123,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_316,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_relset_1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_64,c_309])).

tff(c_320,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_186,c_316])).

tff(c_321,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_320])).

tff(c_173,plain,(
    ! [A_76,B_77,C_78] :
      ( k2_relset_1(A_76,B_77,C_78) = k2_relat_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_177,plain,(
    k2_relset_1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_173])).

tff(c_200,plain,(
    ! [A_86,B_87,C_88] :
      ( m1_subset_1(k2_relset_1(A_86,B_87,C_88),k1_zfmisc_1(B_87))
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_215,plain,
    ( m1_subset_1(k2_relat_1('#skF_6'),k1_zfmisc_1(k1_tarski('#skF_4')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_200])).

tff(c_220,plain,(
    m1_subset_1(k2_relat_1('#skF_6'),k1_zfmisc_1(k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_215])).

tff(c_221,plain,(
    ! [B_89,A_90] :
      ( r2_hidden(k1_funct_1(B_89,A_90),k2_relat_1(B_89))
      | ~ r2_hidden(A_90,k1_relat_1(B_89))
      | ~ v1_funct_1(B_89)
      | ~ v1_relat_1(B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_26,plain,(
    ! [C_14,A_11,B_12] :
      ( r2_hidden(C_14,A_11)
      | ~ r2_hidden(C_14,B_12)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_476,plain,(
    ! [B_140,A_141,A_142] :
      ( r2_hidden(k1_funct_1(B_140,A_141),A_142)
      | ~ m1_subset_1(k2_relat_1(B_140),k1_zfmisc_1(A_142))
      | ~ r2_hidden(A_141,k1_relat_1(B_140))
      | ~ v1_funct_1(B_140)
      | ~ v1_relat_1(B_140) ) ),
    inference(resolution,[status(thm)],[c_221,c_26])).

tff(c_478,plain,(
    ! [A_141] :
      ( r2_hidden(k1_funct_1('#skF_6',A_141),k1_tarski('#skF_4'))
      | ~ r2_hidden(A_141,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_220,c_476])).

tff(c_482,plain,(
    ! [A_143] :
      ( r2_hidden(k1_funct_1('#skF_6',A_143),k1_tarski('#skF_4'))
      | ~ r2_hidden(A_143,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_68,c_321,c_478])).

tff(c_22,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_129,plain,(
    ! [D_58,B_59,A_60] :
      ( D_58 = B_59
      | D_58 = A_60
      | ~ r2_hidden(D_58,k2_tarski(A_60,B_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_138,plain,(
    ! [D_58,A_8] :
      ( D_58 = A_8
      | D_58 = A_8
      | ~ r2_hidden(D_58,k1_tarski(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_129])).

tff(c_500,plain,(
    ! [A_144] :
      ( k1_funct_1('#skF_6',A_144) = '#skF_4'
      | ~ r2_hidden(A_144,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_482,c_138])).

tff(c_513,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_62,c_500])).

tff(c_520,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_513])).

tff(c_521,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_320])).

tff(c_79,plain,(
    ! [D_41,A_42] : r2_hidden(D_41,k2_tarski(A_42,D_41)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_82,plain,(
    ! [A_8] : r2_hidden(A_8,k1_tarski(A_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_79])).

tff(c_89,plain,(
    ! [B_46,A_47] :
      ( ~ r1_tarski(B_46,A_47)
      | ~ r2_hidden(A_47,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_103,plain,(
    ! [A_8] : ~ r1_tarski(k1_tarski(A_8),A_8) ),
    inference(resolution,[status(thm)],[c_82,c_89])).

tff(c_563,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_521,c_103])).

tff(c_571,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_563])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:41:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.77/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.44  
% 2.77/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.44  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 2.77/1.44  
% 2.77/1.44  %Foreground sorts:
% 2.77/1.44  
% 2.77/1.44  
% 2.77/1.44  %Background operators:
% 2.77/1.44  
% 2.77/1.44  
% 2.77/1.44  %Foreground operators:
% 2.77/1.44  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.77/1.44  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.77/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.77/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.77/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.77/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.77/1.44  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.77/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.77/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.77/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.77/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.77/1.44  tff('#skF_5', type, '#skF_5': $i).
% 2.77/1.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.77/1.44  tff('#skF_6', type, '#skF_6': $i).
% 2.77/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.77/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.77/1.44  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.77/1.44  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.77/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.77/1.44  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.77/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.77/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.77/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.77/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.77/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.77/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.77/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.77/1.44  
% 2.99/1.46  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.99/1.46  tff(f_123, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 2.99/1.46  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.99/1.46  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.99/1.46  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.99/1.46  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.99/1.46  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 2.99/1.46  tff(f_73, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 2.99/1.46  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.99/1.46  tff(f_38, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.99/1.46  tff(f_36, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.99/1.46  tff(f_78, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.99/1.46  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.99/1.46  tff(c_60, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.99/1.46  tff(c_62, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.99/1.46  tff(c_64, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.99/1.46  tff(c_124, plain, (![C_55, A_56, B_57]: (v1_relat_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.99/1.46  tff(c_128, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_64, c_124])).
% 2.99/1.46  tff(c_68, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.99/1.46  tff(c_66, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.99/1.46  tff(c_182, plain, (![A_79, B_80, C_81]: (k1_relset_1(A_79, B_80, C_81)=k1_relat_1(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.99/1.46  tff(c_186, plain, (k1_relset_1('#skF_3', k1_tarski('#skF_4'), '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_64, c_182])).
% 2.99/1.46  tff(c_309, plain, (![B_122, A_123, C_124]: (k1_xboole_0=B_122 | k1_relset_1(A_123, B_122, C_124)=A_123 | ~v1_funct_2(C_124, A_123, B_122) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_123, B_122))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.99/1.46  tff(c_316, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_relset_1('#skF_3', k1_tarski('#skF_4'), '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_64, c_309])).
% 2.99/1.46  tff(c_320, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_186, c_316])).
% 2.99/1.46  tff(c_321, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_320])).
% 2.99/1.46  tff(c_173, plain, (![A_76, B_77, C_78]: (k2_relset_1(A_76, B_77, C_78)=k2_relat_1(C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.99/1.46  tff(c_177, plain, (k2_relset_1('#skF_3', k1_tarski('#skF_4'), '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_64, c_173])).
% 2.99/1.46  tff(c_200, plain, (![A_86, B_87, C_88]: (m1_subset_1(k2_relset_1(A_86, B_87, C_88), k1_zfmisc_1(B_87)) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.99/1.46  tff(c_215, plain, (m1_subset_1(k2_relat_1('#skF_6'), k1_zfmisc_1(k1_tarski('#skF_4'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_177, c_200])).
% 2.99/1.46  tff(c_220, plain, (m1_subset_1(k2_relat_1('#skF_6'), k1_zfmisc_1(k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_215])).
% 2.99/1.46  tff(c_221, plain, (![B_89, A_90]: (r2_hidden(k1_funct_1(B_89, A_90), k2_relat_1(B_89)) | ~r2_hidden(A_90, k1_relat_1(B_89)) | ~v1_funct_1(B_89) | ~v1_relat_1(B_89))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.99/1.46  tff(c_26, plain, (![C_14, A_11, B_12]: (r2_hidden(C_14, A_11) | ~r2_hidden(C_14, B_12) | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.99/1.46  tff(c_476, plain, (![B_140, A_141, A_142]: (r2_hidden(k1_funct_1(B_140, A_141), A_142) | ~m1_subset_1(k2_relat_1(B_140), k1_zfmisc_1(A_142)) | ~r2_hidden(A_141, k1_relat_1(B_140)) | ~v1_funct_1(B_140) | ~v1_relat_1(B_140))), inference(resolution, [status(thm)], [c_221, c_26])).
% 2.99/1.46  tff(c_478, plain, (![A_141]: (r2_hidden(k1_funct_1('#skF_6', A_141), k1_tarski('#skF_4')) | ~r2_hidden(A_141, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_220, c_476])).
% 2.99/1.46  tff(c_482, plain, (![A_143]: (r2_hidden(k1_funct_1('#skF_6', A_143), k1_tarski('#skF_4')) | ~r2_hidden(A_143, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_68, c_321, c_478])).
% 2.99/1.46  tff(c_22, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.99/1.46  tff(c_129, plain, (![D_58, B_59, A_60]: (D_58=B_59 | D_58=A_60 | ~r2_hidden(D_58, k2_tarski(A_60, B_59)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.99/1.46  tff(c_138, plain, (![D_58, A_8]: (D_58=A_8 | D_58=A_8 | ~r2_hidden(D_58, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_129])).
% 2.99/1.46  tff(c_500, plain, (![A_144]: (k1_funct_1('#skF_6', A_144)='#skF_4' | ~r2_hidden(A_144, '#skF_3'))), inference(resolution, [status(thm)], [c_482, c_138])).
% 2.99/1.46  tff(c_513, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_62, c_500])).
% 2.99/1.46  tff(c_520, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_513])).
% 2.99/1.46  tff(c_521, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_320])).
% 2.99/1.46  tff(c_79, plain, (![D_41, A_42]: (r2_hidden(D_41, k2_tarski(A_42, D_41)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.99/1.46  tff(c_82, plain, (![A_8]: (r2_hidden(A_8, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_79])).
% 2.99/1.46  tff(c_89, plain, (![B_46, A_47]: (~r1_tarski(B_46, A_47) | ~r2_hidden(A_47, B_46))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.99/1.46  tff(c_103, plain, (![A_8]: (~r1_tarski(k1_tarski(A_8), A_8))), inference(resolution, [status(thm)], [c_82, c_89])).
% 2.99/1.46  tff(c_563, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_521, c_103])).
% 2.99/1.46  tff(c_571, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_563])).
% 2.99/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.46  
% 2.99/1.46  Inference rules
% 2.99/1.46  ----------------------
% 2.99/1.46  #Ref     : 0
% 2.99/1.46  #Sup     : 108
% 2.99/1.46  #Fact    : 0
% 2.99/1.46  #Define  : 0
% 2.99/1.46  #Split   : 2
% 2.99/1.46  #Chain   : 0
% 2.99/1.46  #Close   : 0
% 2.99/1.46  
% 2.99/1.46  Ordering : KBO
% 2.99/1.46  
% 2.99/1.46  Simplification rules
% 2.99/1.46  ----------------------
% 2.99/1.46  #Subsume      : 17
% 2.99/1.46  #Demod        : 46
% 2.99/1.46  #Tautology    : 26
% 2.99/1.46  #SimpNegUnit  : 1
% 2.99/1.46  #BackRed      : 6
% 2.99/1.46  
% 2.99/1.46  #Partial instantiations: 0
% 2.99/1.46  #Strategies tried      : 1
% 2.99/1.46  
% 2.99/1.46  Timing (in seconds)
% 2.99/1.46  ----------------------
% 2.99/1.46  Preprocessing        : 0.32
% 2.99/1.46  Parsing              : 0.16
% 2.99/1.46  CNF conversion       : 0.02
% 2.99/1.46  Main loop            : 0.31
% 2.99/1.46  Inferencing          : 0.11
% 2.99/1.46  Reduction            : 0.10
% 2.99/1.46  Demodulation         : 0.07
% 2.99/1.46  BG Simplification    : 0.02
% 2.99/1.46  Subsumption          : 0.06
% 2.99/1.46  Abstraction          : 0.02
% 2.99/1.46  MUC search           : 0.00
% 2.99/1.46  Cooper               : 0.00
% 2.99/1.46  Total                : 0.66
% 2.99/1.46  Index Insertion      : 0.00
% 2.99/1.46  Index Deletion       : 0.00
% 2.99/1.46  Index Matching       : 0.00
% 2.99/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
