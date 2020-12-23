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
% DateTime   : Thu Dec  3 10:14:42 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 118 expanded)
%              Number of leaves         :   34 (  58 expanded)
%              Depth                    :   10
%              Number of atoms          :   90 ( 244 expanded)
%              Number of equality atoms :   43 ( 110 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_4 > #skF_8 > #skF_5 > #skF_2

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_96,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_84,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
     => ~ ( r2_hidden(A,D)
          & ! [E,F] :
              ~ ( A = k4_tarski(E,F)
                & r2_hidden(E,B)
                & r2_hidden(F,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_relset_1)).

tff(c_42,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_95,plain,(
    ! [B_58,A_59] :
      ( k1_tarski(k1_funct_1(B_58,A_59)) = k2_relat_1(B_58)
      | k1_tarski(A_59) != k1_relat_1(B_58)
      | ~ v1_funct_1(B_58)
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_38,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_6'),'#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_64,plain,(
    ! [A_46,B_47,C_48] :
      ( k2_relset_1(A_46,B_47,C_48) = k2_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_68,plain,(
    k2_relset_1(k1_tarski('#skF_6'),'#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_38,c_64])).

tff(c_34,plain,(
    k2_relset_1(k1_tarski('#skF_6'),'#skF_7','#skF_8') != k1_tarski(k1_funct_1('#skF_8','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_69,plain,(
    k1_tarski(k1_funct_1('#skF_8','#skF_6')) != k2_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_34])).

tff(c_101,plain,
    ( k1_tarski('#skF_6') != k1_relat_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_69])).

tff(c_108,plain,
    ( k1_tarski('#skF_6') != k1_relat_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_101])).

tff(c_110,plain,(
    ~ v1_relat_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_8,plain,(
    ! [A_2] :
      ( r2_hidden('#skF_1'(A_2),A_2)
      | v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_40,plain,(
    v1_funct_2('#skF_8',k1_tarski('#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_55,plain,(
    ! [A_43,B_44,C_45] :
      ( k1_relset_1(A_43,B_44,C_45) = k1_relat_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_59,plain,(
    k1_relset_1(k1_tarski('#skF_6'),'#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_38,c_55])).

tff(c_130,plain,(
    ! [B_77,A_78,C_79] :
      ( k1_xboole_0 = B_77
      | k1_relset_1(A_78,B_77,C_79) = A_78
      | ~ v1_funct_2(C_79,A_78,B_77)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_78,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_133,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1(k1_tarski('#skF_6'),'#skF_7','#skF_8') = k1_tarski('#skF_6')
    | ~ v1_funct_2('#skF_8',k1_tarski('#skF_6'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_38,c_130])).

tff(c_136,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_tarski('#skF_6') = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_59,c_133])).

tff(c_137,plain,(
    k1_tarski('#skF_6') = k1_relat_1('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_136])).

tff(c_142,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_8'),'#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_38])).

tff(c_184,plain,(
    ! [A_80,B_81,C_82,D_83] :
      ( k4_tarski('#skF_4'(A_80,B_81,C_82,D_83),'#skF_5'(A_80,B_81,C_82,D_83)) = A_80
      | ~ r2_hidden(A_80,D_83)
      | ~ m1_subset_1(D_83,k1_zfmisc_1(k2_zfmisc_1(B_81,C_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_192,plain,(
    ! [A_86] :
      ( k4_tarski('#skF_4'(A_86,k1_relat_1('#skF_8'),'#skF_7','#skF_8'),'#skF_5'(A_86,k1_relat_1('#skF_8'),'#skF_7','#skF_8')) = A_86
      | ~ r2_hidden(A_86,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_142,c_184])).

tff(c_6,plain,(
    ! [C_15,D_16,A_2] :
      ( k4_tarski(C_15,D_16) != '#skF_1'(A_2)
      | v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_196,plain,(
    ! [A_86,A_2] :
      ( A_86 != '#skF_1'(A_2)
      | v1_relat_1(A_2)
      | ~ r2_hidden(A_86,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_6])).

tff(c_207,plain,(
    ! [A_89] :
      ( v1_relat_1(A_89)
      | ~ r2_hidden('#skF_1'(A_89),'#skF_8') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_196])).

tff(c_211,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_8,c_207])).

tff(c_215,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_110,c_211])).

tff(c_216,plain,(
    k1_tarski('#skF_6') != k1_relat_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_237,plain,(
    ! [B_107,A_108,C_109] :
      ( k1_xboole_0 = B_107
      | k1_relset_1(A_108,B_107,C_109) = A_108
      | ~ v1_funct_2(C_109,A_108,B_107)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_108,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_240,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1(k1_tarski('#skF_6'),'#skF_7','#skF_8') = k1_tarski('#skF_6')
    | ~ v1_funct_2('#skF_8',k1_tarski('#skF_6'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_38,c_237])).

tff(c_243,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_tarski('#skF_6') = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_59,c_240])).

tff(c_245,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_216,c_36,c_243])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:05:50 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.27/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.27  
% 2.27/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.27  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_4 > #skF_8 > #skF_5 > #skF_2
% 2.27/1.27  
% 2.27/1.27  %Foreground sorts:
% 2.27/1.27  
% 2.27/1.27  
% 2.27/1.27  %Background operators:
% 2.27/1.27  
% 2.27/1.27  
% 2.27/1.27  %Foreground operators:
% 2.27/1.27  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.27/1.27  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.27/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.27/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.27/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.27/1.27  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.27/1.27  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.27/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.27/1.27  tff('#skF_7', type, '#skF_7': $i).
% 2.27/1.27  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.27/1.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.27/1.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.27/1.27  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.27/1.27  tff('#skF_6', type, '#skF_6': $i).
% 2.27/1.27  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.27/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.27/1.27  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.27/1.27  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.27/1.27  tff('#skF_8', type, '#skF_8': $i).
% 2.27/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.27/1.27  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 2.27/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.27/1.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.27/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.27/1.27  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.27/1.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.27/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.27/1.27  
% 2.27/1.28  tff(f_96, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_2)).
% 2.27/1.28  tff(f_45, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 2.27/1.28  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.27/1.28  tff(f_37, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 2.27/1.28  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.27/1.28  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.27/1.28  tff(f_66, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => ~(r2_hidden(A, D) & (![E, F]: ~(((A = k4_tarski(E, F)) & r2_hidden(E, B)) & r2_hidden(F, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_relset_1)).
% 2.27/1.28  tff(c_42, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.27/1.28  tff(c_95, plain, (![B_58, A_59]: (k1_tarski(k1_funct_1(B_58, A_59))=k2_relat_1(B_58) | k1_tarski(A_59)!=k1_relat_1(B_58) | ~v1_funct_1(B_58) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.27/1.28  tff(c_38, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_6'), '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.27/1.28  tff(c_64, plain, (![A_46, B_47, C_48]: (k2_relset_1(A_46, B_47, C_48)=k2_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.27/1.28  tff(c_68, plain, (k2_relset_1(k1_tarski('#skF_6'), '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_38, c_64])).
% 2.27/1.28  tff(c_34, plain, (k2_relset_1(k1_tarski('#skF_6'), '#skF_7', '#skF_8')!=k1_tarski(k1_funct_1('#skF_8', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.27/1.28  tff(c_69, plain, (k1_tarski(k1_funct_1('#skF_8', '#skF_6'))!=k2_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_34])).
% 2.27/1.28  tff(c_101, plain, (k1_tarski('#skF_6')!=k1_relat_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_95, c_69])).
% 2.27/1.28  tff(c_108, plain, (k1_tarski('#skF_6')!=k1_relat_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_101])).
% 2.27/1.28  tff(c_110, plain, (~v1_relat_1('#skF_8')), inference(splitLeft, [status(thm)], [c_108])).
% 2.27/1.28  tff(c_8, plain, (![A_2]: (r2_hidden('#skF_1'(A_2), A_2) | v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.27/1.28  tff(c_36, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.27/1.28  tff(c_40, plain, (v1_funct_2('#skF_8', k1_tarski('#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.27/1.28  tff(c_55, plain, (![A_43, B_44, C_45]: (k1_relset_1(A_43, B_44, C_45)=k1_relat_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.27/1.28  tff(c_59, plain, (k1_relset_1(k1_tarski('#skF_6'), '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_38, c_55])).
% 2.27/1.28  tff(c_130, plain, (![B_77, A_78, C_79]: (k1_xboole_0=B_77 | k1_relset_1(A_78, B_77, C_79)=A_78 | ~v1_funct_2(C_79, A_78, B_77) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_78, B_77))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.27/1.28  tff(c_133, plain, (k1_xboole_0='#skF_7' | k1_relset_1(k1_tarski('#skF_6'), '#skF_7', '#skF_8')=k1_tarski('#skF_6') | ~v1_funct_2('#skF_8', k1_tarski('#skF_6'), '#skF_7')), inference(resolution, [status(thm)], [c_38, c_130])).
% 2.27/1.28  tff(c_136, plain, (k1_xboole_0='#skF_7' | k1_tarski('#skF_6')=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_59, c_133])).
% 2.27/1.28  tff(c_137, plain, (k1_tarski('#skF_6')=k1_relat_1('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_36, c_136])).
% 2.27/1.28  tff(c_142, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_8'), '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_38])).
% 2.27/1.28  tff(c_184, plain, (![A_80, B_81, C_82, D_83]: (k4_tarski('#skF_4'(A_80, B_81, C_82, D_83), '#skF_5'(A_80, B_81, C_82, D_83))=A_80 | ~r2_hidden(A_80, D_83) | ~m1_subset_1(D_83, k1_zfmisc_1(k2_zfmisc_1(B_81, C_82))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.27/1.28  tff(c_192, plain, (![A_86]: (k4_tarski('#skF_4'(A_86, k1_relat_1('#skF_8'), '#skF_7', '#skF_8'), '#skF_5'(A_86, k1_relat_1('#skF_8'), '#skF_7', '#skF_8'))=A_86 | ~r2_hidden(A_86, '#skF_8'))), inference(resolution, [status(thm)], [c_142, c_184])).
% 2.27/1.28  tff(c_6, plain, (![C_15, D_16, A_2]: (k4_tarski(C_15, D_16)!='#skF_1'(A_2) | v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.27/1.28  tff(c_196, plain, (![A_86, A_2]: (A_86!='#skF_1'(A_2) | v1_relat_1(A_2) | ~r2_hidden(A_86, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_192, c_6])).
% 2.27/1.28  tff(c_207, plain, (![A_89]: (v1_relat_1(A_89) | ~r2_hidden('#skF_1'(A_89), '#skF_8'))), inference(reflexivity, [status(thm), theory('equality')], [c_196])).
% 2.27/1.28  tff(c_211, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_8, c_207])).
% 2.27/1.28  tff(c_215, plain, $false, inference(negUnitSimplification, [status(thm)], [c_110, c_110, c_211])).
% 2.27/1.28  tff(c_216, plain, (k1_tarski('#skF_6')!=k1_relat_1('#skF_8')), inference(splitRight, [status(thm)], [c_108])).
% 2.27/1.28  tff(c_237, plain, (![B_107, A_108, C_109]: (k1_xboole_0=B_107 | k1_relset_1(A_108, B_107, C_109)=A_108 | ~v1_funct_2(C_109, A_108, B_107) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_108, B_107))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.27/1.28  tff(c_240, plain, (k1_xboole_0='#skF_7' | k1_relset_1(k1_tarski('#skF_6'), '#skF_7', '#skF_8')=k1_tarski('#skF_6') | ~v1_funct_2('#skF_8', k1_tarski('#skF_6'), '#skF_7')), inference(resolution, [status(thm)], [c_38, c_237])).
% 2.27/1.28  tff(c_243, plain, (k1_xboole_0='#skF_7' | k1_tarski('#skF_6')=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_59, c_240])).
% 2.27/1.28  tff(c_245, plain, $false, inference(negUnitSimplification, [status(thm)], [c_216, c_36, c_243])).
% 2.27/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.28  
% 2.27/1.28  Inference rules
% 2.27/1.28  ----------------------
% 2.27/1.28  #Ref     : 2
% 2.27/1.28  #Sup     : 40
% 2.27/1.28  #Fact    : 0
% 2.27/1.28  #Define  : 0
% 2.27/1.28  #Split   : 1
% 2.27/1.28  #Chain   : 0
% 2.27/1.28  #Close   : 0
% 2.27/1.28  
% 2.27/1.28  Ordering : KBO
% 2.27/1.28  
% 2.27/1.28  Simplification rules
% 2.27/1.28  ----------------------
% 2.27/1.28  #Subsume      : 3
% 2.27/1.28  #Demod        : 22
% 2.27/1.28  #Tautology    : 24
% 2.27/1.28  #SimpNegUnit  : 7
% 2.27/1.28  #BackRed      : 7
% 2.27/1.28  
% 2.27/1.28  #Partial instantiations: 0
% 2.27/1.28  #Strategies tried      : 1
% 2.27/1.28  
% 2.27/1.28  Timing (in seconds)
% 2.27/1.28  ----------------------
% 2.27/1.28  Preprocessing        : 0.31
% 2.27/1.28  Parsing              : 0.16
% 2.27/1.28  CNF conversion       : 0.02
% 2.27/1.28  Main loop            : 0.21
% 2.27/1.28  Inferencing          : 0.08
% 2.27/1.28  Reduction            : 0.06
% 2.27/1.28  Demodulation         : 0.04
% 2.27/1.29  BG Simplification    : 0.01
% 2.27/1.29  Subsumption          : 0.03
% 2.27/1.29  Abstraction          : 0.01
% 2.27/1.29  MUC search           : 0.00
% 2.27/1.29  Cooper               : 0.00
% 2.27/1.29  Total                : 0.55
% 2.27/1.29  Index Insertion      : 0.00
% 2.27/1.29  Index Deletion       : 0.00
% 2.27/1.29  Index Matching       : 0.00
% 2.27/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
