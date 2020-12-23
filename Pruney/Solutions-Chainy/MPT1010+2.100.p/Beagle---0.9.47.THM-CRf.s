%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:18 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   67 (  90 expanded)
%              Number of leaves         :   37 (  49 expanded)
%              Depth                    :    9
%              Number of atoms          :   90 ( 169 expanded)
%              Number of equality atoms :   27 (  52 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_101,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_51,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_90,axiom,(
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

tff(f_62,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_42,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_48,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_52,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_105,plain,(
    ! [C_48,B_49,A_50] :
      ( v5_relat_1(C_48,B_49)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_50,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_109,plain,(
    v5_relat_1('#skF_6',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_52,c_105])).

tff(c_50,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_26,plain,(
    ! [A_16,B_17] : v1_relat_1(k2_zfmisc_1(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_84,plain,(
    ! [B_40,A_41] :
      ( v1_relat_1(B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_41))
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_87,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_52,c_84])).

tff(c_90,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_87])).

tff(c_56,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_54,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_118,plain,(
    ! [A_57,B_58,C_59] :
      ( k1_relset_1(A_57,B_58,C_59) = k1_relat_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_122,plain,(
    k1_relset_1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_118])).

tff(c_180,plain,(
    ! [B_79,A_80,C_81] :
      ( k1_xboole_0 = B_79
      | k1_relset_1(A_80,B_79,C_81) = A_80
      | ~ v1_funct_2(C_81,A_80,B_79)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_80,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_183,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_relset_1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_52,c_180])).

tff(c_186,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_122,c_183])).

tff(c_187,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_186])).

tff(c_160,plain,(
    ! [B_71,C_72,A_73] :
      ( r2_hidden(k1_funct_1(B_71,C_72),A_73)
      | ~ r2_hidden(C_72,k1_relat_1(B_71))
      | ~ v1_funct_1(B_71)
      | ~ v5_relat_1(B_71,A_73)
      | ~ v1_relat_1(B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_4,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_165,plain,(
    ! [B_71,C_72,A_1] :
      ( k1_funct_1(B_71,C_72) = A_1
      | ~ r2_hidden(C_72,k1_relat_1(B_71))
      | ~ v1_funct_1(B_71)
      | ~ v5_relat_1(B_71,k1_tarski(A_1))
      | ~ v1_relat_1(B_71) ) ),
    inference(resolution,[status(thm)],[c_160,c_4])).

tff(c_197,plain,(
    ! [C_72,A_1] :
      ( k1_funct_1('#skF_6',C_72) = A_1
      | ~ r2_hidden(C_72,'#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ v5_relat_1('#skF_6',k1_tarski(A_1))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_165])).

tff(c_207,plain,(
    ! [C_85,A_86] :
      ( k1_funct_1('#skF_6',C_85) = A_86
      | ~ r2_hidden(C_85,'#skF_3')
      | ~ v5_relat_1('#skF_6',k1_tarski(A_86)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_56,c_197])).

tff(c_223,plain,(
    ! [A_87] :
      ( k1_funct_1('#skF_6','#skF_5') = A_87
      | ~ v5_relat_1('#skF_6',k1_tarski(A_87)) ) ),
    inference(resolution,[status(thm)],[c_50,c_207])).

tff(c_226,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_109,c_223])).

tff(c_230,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_226])).

tff(c_231,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_22,plain,(
    ! [A_12] : ~ v1_xboole_0(k1_tarski(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_254,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_22])).

tff(c_262,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_254])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:55:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.26  
% 2.28/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.26  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.28/1.26  
% 2.28/1.26  %Foreground sorts:
% 2.28/1.26  
% 2.28/1.26  
% 2.28/1.26  %Background operators:
% 2.28/1.26  
% 2.28/1.26  
% 2.28/1.26  %Foreground operators:
% 2.28/1.26  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.28/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.28/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.28/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.28/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.28/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.28/1.26  tff('#skF_5', type, '#skF_5': $i).
% 2.28/1.26  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.28/1.26  tff('#skF_6', type, '#skF_6': $i).
% 2.28/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.28/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.28/1.26  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.28/1.26  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.28/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.28/1.26  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.28/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.28/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.28/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.28/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.26  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.28/1.26  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.28/1.26  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.28/1.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.28/1.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.28/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.28/1.26  
% 2.41/1.28  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.41/1.28  tff(f_101, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 2.41/1.28  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.41/1.28  tff(f_51, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.41/1.28  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.41/1.28  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.41/1.28  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.41/1.28  tff(f_62, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_1)).
% 2.41/1.28  tff(f_33, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.41/1.28  tff(f_42, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 2.41/1.28  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.41/1.28  tff(c_48, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.41/1.28  tff(c_52, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.41/1.28  tff(c_105, plain, (![C_48, B_49, A_50]: (v5_relat_1(C_48, B_49) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_50, B_49))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.41/1.28  tff(c_109, plain, (v5_relat_1('#skF_6', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_52, c_105])).
% 2.41/1.28  tff(c_50, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.41/1.28  tff(c_26, plain, (![A_16, B_17]: (v1_relat_1(k2_zfmisc_1(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.41/1.28  tff(c_84, plain, (![B_40, A_41]: (v1_relat_1(B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(A_41)) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.41/1.28  tff(c_87, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))), inference(resolution, [status(thm)], [c_52, c_84])).
% 2.41/1.28  tff(c_90, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_87])).
% 2.41/1.28  tff(c_56, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.41/1.28  tff(c_54, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.41/1.28  tff(c_118, plain, (![A_57, B_58, C_59]: (k1_relset_1(A_57, B_58, C_59)=k1_relat_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.41/1.28  tff(c_122, plain, (k1_relset_1('#skF_3', k1_tarski('#skF_4'), '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_52, c_118])).
% 2.41/1.28  tff(c_180, plain, (![B_79, A_80, C_81]: (k1_xboole_0=B_79 | k1_relset_1(A_80, B_79, C_81)=A_80 | ~v1_funct_2(C_81, A_80, B_79) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_80, B_79))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.41/1.28  tff(c_183, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_relset_1('#skF_3', k1_tarski('#skF_4'), '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_52, c_180])).
% 2.41/1.28  tff(c_186, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_122, c_183])).
% 2.41/1.28  tff(c_187, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_186])).
% 2.41/1.28  tff(c_160, plain, (![B_71, C_72, A_73]: (r2_hidden(k1_funct_1(B_71, C_72), A_73) | ~r2_hidden(C_72, k1_relat_1(B_71)) | ~v1_funct_1(B_71) | ~v5_relat_1(B_71, A_73) | ~v1_relat_1(B_71))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.41/1.28  tff(c_4, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.41/1.28  tff(c_165, plain, (![B_71, C_72, A_1]: (k1_funct_1(B_71, C_72)=A_1 | ~r2_hidden(C_72, k1_relat_1(B_71)) | ~v1_funct_1(B_71) | ~v5_relat_1(B_71, k1_tarski(A_1)) | ~v1_relat_1(B_71))), inference(resolution, [status(thm)], [c_160, c_4])).
% 2.41/1.28  tff(c_197, plain, (![C_72, A_1]: (k1_funct_1('#skF_6', C_72)=A_1 | ~r2_hidden(C_72, '#skF_3') | ~v1_funct_1('#skF_6') | ~v5_relat_1('#skF_6', k1_tarski(A_1)) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_187, c_165])).
% 2.41/1.28  tff(c_207, plain, (![C_85, A_86]: (k1_funct_1('#skF_6', C_85)=A_86 | ~r2_hidden(C_85, '#skF_3') | ~v5_relat_1('#skF_6', k1_tarski(A_86)))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_56, c_197])).
% 2.41/1.28  tff(c_223, plain, (![A_87]: (k1_funct_1('#skF_6', '#skF_5')=A_87 | ~v5_relat_1('#skF_6', k1_tarski(A_87)))), inference(resolution, [status(thm)], [c_50, c_207])).
% 2.41/1.28  tff(c_226, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_109, c_223])).
% 2.41/1.28  tff(c_230, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_226])).
% 2.41/1.28  tff(c_231, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_186])).
% 2.41/1.28  tff(c_22, plain, (![A_12]: (~v1_xboole_0(k1_tarski(A_12)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.41/1.28  tff(c_254, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_231, c_22])).
% 2.41/1.28  tff(c_262, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_254])).
% 2.41/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/1.28  
% 2.41/1.28  Inference rules
% 2.41/1.28  ----------------------
% 2.41/1.28  #Ref     : 0
% 2.41/1.28  #Sup     : 44
% 2.41/1.28  #Fact    : 0
% 2.41/1.28  #Define  : 0
% 2.41/1.28  #Split   : 1
% 2.41/1.28  #Chain   : 0
% 2.41/1.28  #Close   : 0
% 2.41/1.28  
% 2.41/1.28  Ordering : KBO
% 2.41/1.28  
% 2.41/1.28  Simplification rules
% 2.41/1.28  ----------------------
% 2.41/1.28  #Subsume      : 0
% 2.41/1.28  #Demod        : 23
% 2.41/1.28  #Tautology    : 20
% 2.41/1.28  #SimpNegUnit  : 1
% 2.41/1.28  #BackRed      : 5
% 2.41/1.28  
% 2.41/1.28  #Partial instantiations: 0
% 2.41/1.28  #Strategies tried      : 1
% 2.41/1.28  
% 2.41/1.28  Timing (in seconds)
% 2.41/1.28  ----------------------
% 2.41/1.28  Preprocessing        : 0.32
% 2.41/1.28  Parsing              : 0.17
% 2.41/1.28  CNF conversion       : 0.02
% 2.41/1.28  Main loop            : 0.21
% 2.41/1.28  Inferencing          : 0.08
% 2.41/1.28  Reduction            : 0.06
% 2.41/1.28  Demodulation         : 0.04
% 2.41/1.28  BG Simplification    : 0.02
% 2.41/1.28  Subsumption          : 0.04
% 2.41/1.28  Abstraction          : 0.01
% 2.41/1.28  MUC search           : 0.00
% 2.41/1.28  Cooper               : 0.00
% 2.41/1.28  Total                : 0.56
% 2.41/1.28  Index Insertion      : 0.00
% 2.41/1.28  Index Deletion       : 0.00
% 2.41/1.28  Index Matching       : 0.00
% 2.41/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
