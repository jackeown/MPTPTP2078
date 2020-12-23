%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:22 EST 2020

% Result     : Theorem 6.27s
% Output     : CNFRefutation 6.27s
% Verified   : 
% Statistics : Number of formulae       :   66 (  78 expanded)
%              Number of leaves         :   35 (  43 expanded)
%              Depth                    :    8
%              Number of atoms          :   93 ( 137 expanded)
%              Number of equality atoms :   26 (  34 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff(f_104,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_92,axiom,(
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

tff(f_54,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_56,plain,(
    v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_135,plain,(
    ! [A_62,B_63,C_64] :
      ( k1_relset_1(A_62,B_63,C_64) = k1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_139,plain,(
    k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_135])).

tff(c_226,plain,(
    ! [B_94,A_95,C_96] :
      ( k1_xboole_0 = B_94
      | k1_relset_1(A_95,B_94,C_96) = A_95
      | ~ v1_funct_2(C_96,A_95,B_94)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_95,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_233,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_tarski('#skF_3')
    | ~ v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_226])).

tff(c_237,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_tarski('#skF_3') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_139,c_233])).

tff(c_238,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_237])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_69,plain,(
    ! [D_36,A_37] : r2_hidden(D_36,k2_tarski(A_37,D_36)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_72,plain,(
    ! [A_7] : r2_hidden(A_7,k1_tarski(A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_69])).

tff(c_252,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_72])).

tff(c_28,plain,(
    ! [A_17,B_18] : v1_relat_1(k2_zfmisc_1(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_88,plain,(
    ! [B_43,A_44] :
      ( v1_relat_1(B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_44))
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_91,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_54,c_88])).

tff(c_94,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_91])).

tff(c_58,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_144,plain,(
    ! [A_65,B_66,C_67] :
      ( k2_relset_1(A_65,B_66,C_67) = k2_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_148,plain,(
    k2_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_144])).

tff(c_153,plain,(
    ! [A_68,B_69,C_70] :
      ( m1_subset_1(k2_relset_1(A_68,B_69,C_70),k1_zfmisc_1(B_69))
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_167,plain,
    ( m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_153])).

tff(c_172,plain,(
    m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_167])).

tff(c_173,plain,(
    ! [B_71,A_72] :
      ( r2_hidden(k1_funct_1(B_71,A_72),k2_relat_1(B_71))
      | ~ r2_hidden(A_72,k1_relat_1(B_71))
      | ~ v1_funct_1(B_71)
      | ~ v1_relat_1(B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_24,plain,(
    ! [C_13,A_10,B_11] :
      ( r2_hidden(C_13,A_10)
      | ~ r2_hidden(C_13,B_11)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6177,plain,(
    ! [B_8305,A_8306,A_8307] :
      ( r2_hidden(k1_funct_1(B_8305,A_8306),A_8307)
      | ~ m1_subset_1(k2_relat_1(B_8305),k1_zfmisc_1(A_8307))
      | ~ r2_hidden(A_8306,k1_relat_1(B_8305))
      | ~ v1_funct_1(B_8305)
      | ~ v1_relat_1(B_8305) ) ),
    inference(resolution,[status(thm)],[c_173,c_24])).

tff(c_6187,plain,(
    ! [A_8306] :
      ( r2_hidden(k1_funct_1('#skF_5',A_8306),'#skF_4')
      | ~ r2_hidden(A_8306,k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_172,c_6177])).

tff(c_6191,plain,(
    ! [A_8408] :
      ( r2_hidden(k1_funct_1('#skF_5',A_8408),'#skF_4')
      | ~ r2_hidden(A_8408,k1_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_58,c_6187])).

tff(c_50,plain,(
    ~ r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_6198,plain,(
    ~ r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_6191,c_50])).

tff(c_6208,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_6198])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:11:46 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.27/2.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.27/2.25  
% 6.27/2.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.27/2.25  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 6.27/2.25  
% 6.27/2.25  %Foreground sorts:
% 6.27/2.25  
% 6.27/2.25  
% 6.27/2.25  %Background operators:
% 6.27/2.25  
% 6.27/2.25  
% 6.27/2.25  %Foreground operators:
% 6.27/2.25  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.27/2.25  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.27/2.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.27/2.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.27/2.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.27/2.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.27/2.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.27/2.25  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.27/2.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.27/2.25  tff('#skF_5', type, '#skF_5': $i).
% 6.27/2.25  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.27/2.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.27/2.25  tff('#skF_3', type, '#skF_3': $i).
% 6.27/2.25  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.27/2.25  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.27/2.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.27/2.25  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.27/2.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.27/2.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.27/2.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.27/2.25  tff('#skF_4', type, '#skF_4': $i).
% 6.27/2.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.27/2.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.27/2.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.27/2.25  
% 6.27/2.26  tff(f_104, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_2)).
% 6.27/2.26  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.27/2.26  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.27/2.26  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 6.27/2.26  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 6.27/2.26  tff(f_54, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.27/2.26  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.27/2.26  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.27/2.26  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 6.27/2.26  tff(f_62, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 6.27/2.26  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 6.27/2.26  tff(c_52, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.27/2.26  tff(c_56, plain, (v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.27/2.26  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.27/2.26  tff(c_135, plain, (![A_62, B_63, C_64]: (k1_relset_1(A_62, B_63, C_64)=k1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.27/2.26  tff(c_139, plain, (k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_135])).
% 6.27/2.26  tff(c_226, plain, (![B_94, A_95, C_96]: (k1_xboole_0=B_94 | k1_relset_1(A_95, B_94, C_96)=A_95 | ~v1_funct_2(C_96, A_95, B_94) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_95, B_94))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.27/2.26  tff(c_233, plain, (k1_xboole_0='#skF_4' | k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_tarski('#skF_3') | ~v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_54, c_226])).
% 6.27/2.26  tff(c_237, plain, (k1_xboole_0='#skF_4' | k1_tarski('#skF_3')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_139, c_233])).
% 6.27/2.26  tff(c_238, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_52, c_237])).
% 6.27/2.26  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.27/2.26  tff(c_69, plain, (![D_36, A_37]: (r2_hidden(D_36, k2_tarski(A_37, D_36)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.27/2.26  tff(c_72, plain, (![A_7]: (r2_hidden(A_7, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_69])).
% 6.27/2.26  tff(c_252, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_238, c_72])).
% 6.27/2.26  tff(c_28, plain, (![A_17, B_18]: (v1_relat_1(k2_zfmisc_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.27/2.26  tff(c_88, plain, (![B_43, A_44]: (v1_relat_1(B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(A_44)) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.27/2.26  tff(c_91, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4'))), inference(resolution, [status(thm)], [c_54, c_88])).
% 6.27/2.26  tff(c_94, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_91])).
% 6.27/2.26  tff(c_58, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.27/2.26  tff(c_144, plain, (![A_65, B_66, C_67]: (k2_relset_1(A_65, B_66, C_67)=k2_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.27/2.26  tff(c_148, plain, (k2_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_144])).
% 6.27/2.26  tff(c_153, plain, (![A_68, B_69, C_70]: (m1_subset_1(k2_relset_1(A_68, B_69, C_70), k1_zfmisc_1(B_69)) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.27/2.26  tff(c_167, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_148, c_153])).
% 6.27/2.26  tff(c_172, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_167])).
% 6.27/2.26  tff(c_173, plain, (![B_71, A_72]: (r2_hidden(k1_funct_1(B_71, A_72), k2_relat_1(B_71)) | ~r2_hidden(A_72, k1_relat_1(B_71)) | ~v1_funct_1(B_71) | ~v1_relat_1(B_71))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.27/2.26  tff(c_24, plain, (![C_13, A_10, B_11]: (r2_hidden(C_13, A_10) | ~r2_hidden(C_13, B_11) | ~m1_subset_1(B_11, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.27/2.26  tff(c_6177, plain, (![B_8305, A_8306, A_8307]: (r2_hidden(k1_funct_1(B_8305, A_8306), A_8307) | ~m1_subset_1(k2_relat_1(B_8305), k1_zfmisc_1(A_8307)) | ~r2_hidden(A_8306, k1_relat_1(B_8305)) | ~v1_funct_1(B_8305) | ~v1_relat_1(B_8305))), inference(resolution, [status(thm)], [c_173, c_24])).
% 6.27/2.26  tff(c_6187, plain, (![A_8306]: (r2_hidden(k1_funct_1('#skF_5', A_8306), '#skF_4') | ~r2_hidden(A_8306, k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_172, c_6177])).
% 6.27/2.26  tff(c_6191, plain, (![A_8408]: (r2_hidden(k1_funct_1('#skF_5', A_8408), '#skF_4') | ~r2_hidden(A_8408, k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_58, c_6187])).
% 6.27/2.26  tff(c_50, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.27/2.26  tff(c_6198, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_6191, c_50])).
% 6.27/2.26  tff(c_6208, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_252, c_6198])).
% 6.27/2.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.27/2.26  
% 6.27/2.26  Inference rules
% 6.27/2.26  ----------------------
% 6.27/2.26  #Ref     : 0
% 6.27/2.26  #Sup     : 986
% 6.27/2.26  #Fact    : 34
% 6.27/2.26  #Define  : 0
% 6.27/2.26  #Split   : 5
% 6.27/2.26  #Chain   : 0
% 6.27/2.26  #Close   : 0
% 6.27/2.26  
% 6.27/2.26  Ordering : KBO
% 6.27/2.26  
% 6.27/2.26  Simplification rules
% 6.27/2.26  ----------------------
% 6.27/2.26  #Subsume      : 390
% 6.27/2.26  #Demod        : 104
% 6.27/2.26  #Tautology    : 325
% 6.27/2.26  #SimpNegUnit  : 73
% 6.27/2.26  #BackRed      : 4
% 6.27/2.26  
% 6.27/2.26  #Partial instantiations: 4565
% 6.27/2.26  #Strategies tried      : 1
% 6.27/2.26  
% 6.27/2.26  Timing (in seconds)
% 6.27/2.26  ----------------------
% 6.27/2.26  Preprocessing        : 0.34
% 6.27/2.26  Parsing              : 0.18
% 6.27/2.26  CNF conversion       : 0.02
% 6.27/2.26  Main loop            : 1.15
% 6.27/2.26  Inferencing          : 0.55
% 6.27/2.27  Reduction            : 0.27
% 6.27/2.27  Demodulation         : 0.18
% 6.27/2.27  BG Simplification    : 0.05
% 6.27/2.27  Subsumption          : 0.23
% 6.27/2.27  Abstraction          : 0.06
% 6.27/2.27  MUC search           : 0.00
% 6.27/2.27  Cooper               : 0.00
% 6.27/2.27  Total                : 1.52
% 6.27/2.27  Index Insertion      : 0.00
% 6.27/2.27  Index Deletion       : 0.00
% 6.27/2.27  Index Matching       : 0.00
% 6.27/2.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
