%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:08 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   71 (  97 expanded)
%              Number of leaves         :   38 (  52 expanded)
%              Depth                    :    9
%              Number of atoms          :   96 ( 181 expanded)
%              Number of equality atoms :   33 (  63 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_114,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_85,axiom,(
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

tff(f_66,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_53,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_71,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_74,plain,(
    k1_funct_1('#skF_8','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_78,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_207,plain,(
    ! [C_81,B_82,A_83] :
      ( v5_relat_1(C_81,B_82)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_83,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_211,plain,(
    v5_relat_1('#skF_8',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_78,c_207])).

tff(c_76,plain,(
    r2_hidden('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_165,plain,(
    ! [C_61,A_62,B_63] :
      ( v1_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_169,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_78,c_165])).

tff(c_82,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_80,plain,(
    v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_212,plain,(
    ! [A_84,B_85,C_86] :
      ( k1_relset_1(A_84,B_85,C_86) = k1_relat_1(C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_216,plain,(
    k1_relset_1('#skF_5',k1_tarski('#skF_6'),'#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_78,c_212])).

tff(c_312,plain,(
    ! [B_121,A_122,C_123] :
      ( k1_xboole_0 = B_121
      | k1_relset_1(A_122,B_121,C_123) = A_122
      | ~ v1_funct_2(C_123,A_122,B_121)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_122,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_315,plain,
    ( k1_tarski('#skF_6') = k1_xboole_0
    | k1_relset_1('#skF_5',k1_tarski('#skF_6'),'#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_78,c_312])).

tff(c_318,plain,
    ( k1_tarski('#skF_6') = k1_xboole_0
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_216,c_315])).

tff(c_319,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_318])).

tff(c_266,plain,(
    ! [B_107,C_108,A_109] :
      ( r2_hidden(k1_funct_1(B_107,C_108),A_109)
      | ~ r2_hidden(C_108,k1_relat_1(B_107))
      | ~ v1_funct_1(B_107)
      | ~ v5_relat_1(B_107,A_109)
      | ~ v1_relat_1(B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_46,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_187,plain,(
    ! [D_76,B_77,A_78] :
      ( D_76 = B_77
      | D_76 = A_78
      | ~ r2_hidden(D_76,k2_tarski(A_78,B_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_196,plain,(
    ! [D_76,A_15] :
      ( D_76 = A_15
      | D_76 = A_15
      | ~ r2_hidden(D_76,k1_tarski(A_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_187])).

tff(c_283,plain,(
    ! [B_107,C_108,A_15] :
      ( k1_funct_1(B_107,C_108) = A_15
      | ~ r2_hidden(C_108,k1_relat_1(B_107))
      | ~ v1_funct_1(B_107)
      | ~ v5_relat_1(B_107,k1_tarski(A_15))
      | ~ v1_relat_1(B_107) ) ),
    inference(resolution,[status(thm)],[c_266,c_196])).

tff(c_323,plain,(
    ! [C_108,A_15] :
      ( k1_funct_1('#skF_8',C_108) = A_15
      | ~ r2_hidden(C_108,'#skF_5')
      | ~ v1_funct_1('#skF_8')
      | ~ v5_relat_1('#skF_8',k1_tarski(A_15))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_319,c_283])).

tff(c_339,plain,(
    ! [C_124,A_125] :
      ( k1_funct_1('#skF_8',C_124) = A_125
      | ~ r2_hidden(C_124,'#skF_5')
      | ~ v5_relat_1('#skF_8',k1_tarski(A_125)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_82,c_323])).

tff(c_351,plain,(
    ! [A_126] :
      ( k1_funct_1('#skF_8','#skF_7') = A_126
      | ~ v5_relat_1('#skF_8',k1_tarski(A_126)) ) ),
    inference(resolution,[status(thm)],[c_76,c_339])).

tff(c_354,plain,(
    k1_funct_1('#skF_8','#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_211,c_351])).

tff(c_358,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_354])).

tff(c_359,plain,(
    k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_318])).

tff(c_93,plain,(
    ! [D_38,A_39] : r2_hidden(D_38,k2_tarski(A_39,D_38)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_96,plain,(
    ! [A_15] : r2_hidden(A_15,k1_tarski(A_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_93])).

tff(c_106,plain,(
    ! [B_52,A_53] :
      ( ~ r1_tarski(B_52,A_53)
      | ~ r2_hidden(A_53,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_132,plain,(
    ! [A_15] : ~ r1_tarski(k1_tarski(A_15),A_15) ),
    inference(resolution,[status(thm)],[c_96,c_106])).

tff(c_371,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_359,c_132])).

tff(c_379,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_371])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:59:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.76/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.37  
% 2.76/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.37  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_3 > #skF_1
% 2.76/1.37  
% 2.76/1.37  %Foreground sorts:
% 2.76/1.37  
% 2.76/1.37  
% 2.76/1.37  %Background operators:
% 2.76/1.37  
% 2.76/1.37  
% 2.76/1.37  %Foreground operators:
% 2.76/1.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.76/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.76/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.76/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.76/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.76/1.37  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.76/1.37  tff('#skF_7', type, '#skF_7': $i).
% 2.76/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.76/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.76/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.76/1.37  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.76/1.37  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.76/1.37  tff('#skF_6', type, '#skF_6': $i).
% 2.76/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.76/1.37  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.76/1.37  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.76/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.76/1.37  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.76/1.37  tff('#skF_8', type, '#skF_8': $i).
% 2.76/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.76/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.76/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.76/1.37  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.76/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.76/1.37  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.76/1.37  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.76/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.76/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.76/1.37  
% 2.76/1.39  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.76/1.39  tff(f_114, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 2.76/1.39  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.76/1.39  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.76/1.39  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.76/1.39  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.76/1.39  tff(f_66, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_1)).
% 2.76/1.39  tff(f_53, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.76/1.39  tff(f_51, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.76/1.39  tff(f_71, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.76/1.39  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.76/1.39  tff(c_74, plain, (k1_funct_1('#skF_8', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.76/1.39  tff(c_78, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.76/1.39  tff(c_207, plain, (![C_81, B_82, A_83]: (v5_relat_1(C_81, B_82) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_83, B_82))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.76/1.39  tff(c_211, plain, (v5_relat_1('#skF_8', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_78, c_207])).
% 2.76/1.39  tff(c_76, plain, (r2_hidden('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.76/1.39  tff(c_165, plain, (![C_61, A_62, B_63]: (v1_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.76/1.39  tff(c_169, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_78, c_165])).
% 2.76/1.39  tff(c_82, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.76/1.39  tff(c_80, plain, (v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.76/1.39  tff(c_212, plain, (![A_84, B_85, C_86]: (k1_relset_1(A_84, B_85, C_86)=k1_relat_1(C_86) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.76/1.39  tff(c_216, plain, (k1_relset_1('#skF_5', k1_tarski('#skF_6'), '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_78, c_212])).
% 2.76/1.39  tff(c_312, plain, (![B_121, A_122, C_123]: (k1_xboole_0=B_121 | k1_relset_1(A_122, B_121, C_123)=A_122 | ~v1_funct_2(C_123, A_122, B_121) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_122, B_121))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.76/1.39  tff(c_315, plain, (k1_tarski('#skF_6')=k1_xboole_0 | k1_relset_1('#skF_5', k1_tarski('#skF_6'), '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_78, c_312])).
% 2.76/1.39  tff(c_318, plain, (k1_tarski('#skF_6')=k1_xboole_0 | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_216, c_315])).
% 2.76/1.39  tff(c_319, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(splitLeft, [status(thm)], [c_318])).
% 2.76/1.39  tff(c_266, plain, (![B_107, C_108, A_109]: (r2_hidden(k1_funct_1(B_107, C_108), A_109) | ~r2_hidden(C_108, k1_relat_1(B_107)) | ~v1_funct_1(B_107) | ~v5_relat_1(B_107, A_109) | ~v1_relat_1(B_107))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.76/1.39  tff(c_46, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.76/1.39  tff(c_187, plain, (![D_76, B_77, A_78]: (D_76=B_77 | D_76=A_78 | ~r2_hidden(D_76, k2_tarski(A_78, B_77)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.76/1.39  tff(c_196, plain, (![D_76, A_15]: (D_76=A_15 | D_76=A_15 | ~r2_hidden(D_76, k1_tarski(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_187])).
% 2.76/1.39  tff(c_283, plain, (![B_107, C_108, A_15]: (k1_funct_1(B_107, C_108)=A_15 | ~r2_hidden(C_108, k1_relat_1(B_107)) | ~v1_funct_1(B_107) | ~v5_relat_1(B_107, k1_tarski(A_15)) | ~v1_relat_1(B_107))), inference(resolution, [status(thm)], [c_266, c_196])).
% 2.76/1.39  tff(c_323, plain, (![C_108, A_15]: (k1_funct_1('#skF_8', C_108)=A_15 | ~r2_hidden(C_108, '#skF_5') | ~v1_funct_1('#skF_8') | ~v5_relat_1('#skF_8', k1_tarski(A_15)) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_319, c_283])).
% 2.76/1.39  tff(c_339, plain, (![C_124, A_125]: (k1_funct_1('#skF_8', C_124)=A_125 | ~r2_hidden(C_124, '#skF_5') | ~v5_relat_1('#skF_8', k1_tarski(A_125)))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_82, c_323])).
% 2.76/1.39  tff(c_351, plain, (![A_126]: (k1_funct_1('#skF_8', '#skF_7')=A_126 | ~v5_relat_1('#skF_8', k1_tarski(A_126)))), inference(resolution, [status(thm)], [c_76, c_339])).
% 2.76/1.39  tff(c_354, plain, (k1_funct_1('#skF_8', '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_211, c_351])).
% 2.76/1.39  tff(c_358, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_354])).
% 2.76/1.39  tff(c_359, plain, (k1_tarski('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_318])).
% 2.76/1.39  tff(c_93, plain, (![D_38, A_39]: (r2_hidden(D_38, k2_tarski(A_39, D_38)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.76/1.39  tff(c_96, plain, (![A_15]: (r2_hidden(A_15, k1_tarski(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_93])).
% 2.76/1.39  tff(c_106, plain, (![B_52, A_53]: (~r1_tarski(B_52, A_53) | ~r2_hidden(A_53, B_52))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.76/1.39  tff(c_132, plain, (![A_15]: (~r1_tarski(k1_tarski(A_15), A_15))), inference(resolution, [status(thm)], [c_96, c_106])).
% 2.76/1.39  tff(c_371, plain, (~r1_tarski(k1_xboole_0, '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_359, c_132])).
% 2.76/1.39  tff(c_379, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_371])).
% 2.76/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.39  
% 2.76/1.39  Inference rules
% 2.76/1.39  ----------------------
% 2.76/1.39  #Ref     : 0
% 2.76/1.39  #Sup     : 64
% 2.76/1.39  #Fact    : 0
% 2.76/1.39  #Define  : 0
% 2.76/1.39  #Split   : 2
% 2.76/1.39  #Chain   : 0
% 2.76/1.39  #Close   : 0
% 2.76/1.39  
% 2.76/1.39  Ordering : KBO
% 2.76/1.39  
% 2.76/1.39  Simplification rules
% 2.76/1.39  ----------------------
% 2.76/1.39  #Subsume      : 7
% 2.76/1.39  #Demod        : 16
% 2.76/1.39  #Tautology    : 21
% 2.76/1.39  #SimpNegUnit  : 1
% 2.76/1.39  #BackRed      : 5
% 2.76/1.39  
% 2.76/1.39  #Partial instantiations: 0
% 2.76/1.39  #Strategies tried      : 1
% 2.76/1.39  
% 2.76/1.39  Timing (in seconds)
% 2.76/1.39  ----------------------
% 2.76/1.39  Preprocessing        : 0.36
% 2.76/1.39  Parsing              : 0.18
% 2.76/1.39  CNF conversion       : 0.03
% 2.76/1.39  Main loop            : 0.27
% 2.76/1.39  Inferencing          : 0.09
% 2.76/1.39  Reduction            : 0.08
% 2.76/1.39  Demodulation         : 0.06
% 2.76/1.39  BG Simplification    : 0.02
% 2.76/1.39  Subsumption          : 0.05
% 2.76/1.39  Abstraction          : 0.02
% 2.76/1.39  MUC search           : 0.00
% 2.76/1.39  Cooper               : 0.00
% 2.76/1.39  Total                : 0.67
% 2.76/1.39  Index Insertion      : 0.00
% 2.76/1.39  Index Deletion       : 0.00
% 2.76/1.39  Index Matching       : 0.00
% 2.76/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
