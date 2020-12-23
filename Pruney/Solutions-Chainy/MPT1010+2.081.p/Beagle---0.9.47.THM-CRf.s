%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:16 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 104 expanded)
%              Number of leaves         :   38 (  54 expanded)
%              Depth                    :   11
%              Number of atoms          :  103 ( 204 expanded)
%              Number of equality atoms :   31 (  58 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_108,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_97,axiom,(
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

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_41,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,k1_tarski(D)))
    <=> ( r2_hidden(A,C)
        & B = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_48,plain,(
    k1_funct_1('#skF_5','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_50,plain,(
    r2_hidden('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_tarski('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_76,plain,(
    ! [C_38,A_39,B_40] :
      ( v1_relat_1(C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_80,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_76])).

tff(c_56,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_54,plain,(
    v1_funct_2('#skF_5','#skF_2',k1_tarski('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_120,plain,(
    ! [A_61,B_62,C_63] :
      ( k1_relset_1(A_61,B_62,C_63) = k1_relat_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_124,plain,(
    k1_relset_1('#skF_2',k1_tarski('#skF_3'),'#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_120])).

tff(c_180,plain,(
    ! [B_92,A_93,C_94] :
      ( k1_xboole_0 = B_92
      | k1_relset_1(A_93,B_92,C_94) = A_93
      | ~ v1_funct_2(C_94,A_93,B_92)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_93,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_183,plain,
    ( k1_tarski('#skF_3') = k1_xboole_0
    | k1_relset_1('#skF_2',k1_tarski('#skF_3'),'#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_52,c_180])).

tff(c_186,plain,
    ( k1_tarski('#skF_3') = k1_xboole_0
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_124,c_183])).

tff(c_187,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_186])).

tff(c_30,plain,(
    ! [B_24,A_23] :
      ( r2_hidden(k1_funct_1(B_24,A_23),k2_relat_1(B_24))
      | ~ r2_hidden(A_23,k1_relat_1(B_24))
      | ~ v1_funct_1(B_24)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_28,plain,(
    ! [A_22] :
      ( k9_relat_1(A_22,k1_relat_1(A_22)) = k2_relat_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_143,plain,(
    ! [A_76,B_77,C_78] :
      ( r2_hidden(k4_tarski('#skF_1'(A_76,B_77,C_78),A_76),C_78)
      | ~ r2_hidden(A_76,k9_relat_1(C_78,B_77))
      | ~ v1_relat_1(C_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_18,plain,(
    ! [C_15,A_12,B_13] :
      ( r2_hidden(C_15,A_12)
      | ~ r2_hidden(C_15,B_13)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_273,plain,(
    ! [A_117,B_118,C_119,A_120] :
      ( r2_hidden(k4_tarski('#skF_1'(A_117,B_118,C_119),A_117),A_120)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(A_120))
      | ~ r2_hidden(A_117,k9_relat_1(C_119,B_118))
      | ~ v1_relat_1(C_119) ) ),
    inference(resolution,[status(thm)],[c_143,c_18])).

tff(c_14,plain,(
    ! [D_11,B_9,A_8,C_10] :
      ( D_11 = B_9
      | ~ r2_hidden(k4_tarski(A_8,B_9),k2_zfmisc_1(C_10,k1_tarski(D_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_295,plain,(
    ! [C_121,B_122,A_123,D_125,C_124] :
      ( D_125 = A_123
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(C_124,k1_tarski(D_125))))
      | ~ r2_hidden(A_123,k9_relat_1(C_121,B_122))
      | ~ v1_relat_1(C_121) ) ),
    inference(resolution,[status(thm)],[c_273,c_14])).

tff(c_297,plain,(
    ! [A_123,B_122] :
      ( A_123 = '#skF_3'
      | ~ r2_hidden(A_123,k9_relat_1('#skF_5',B_122))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_52,c_295])).

tff(c_313,plain,(
    ! [A_130,B_131] :
      ( A_130 = '#skF_3'
      | ~ r2_hidden(A_130,k9_relat_1('#skF_5',B_131)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_297])).

tff(c_343,plain,(
    ! [A_130] :
      ( A_130 = '#skF_3'
      | ~ r2_hidden(A_130,k2_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_313])).

tff(c_352,plain,(
    ! [A_132] :
      ( A_132 = '#skF_3'
      | ~ r2_hidden(A_132,k2_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_343])).

tff(c_376,plain,(
    ! [A_23] :
      ( k1_funct_1('#skF_5',A_23) = '#skF_3'
      | ~ r2_hidden(A_23,k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_30,c_352])).

tff(c_391,plain,(
    ! [A_135] :
      ( k1_funct_1('#skF_5',A_135) = '#skF_3'
      | ~ r2_hidden(A_135,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_56,c_187,c_376])).

tff(c_421,plain,(
    k1_funct_1('#skF_5','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_50,c_391])).

tff(c_432,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_421])).

tff(c_433,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_10,plain,(
    ! [A_7] : ~ v1_xboole_0(k1_tarski(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_453,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_433,c_10])).

tff(c_459,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_453])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:22:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.47/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.45  
% 2.47/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.46  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 2.87/1.46  
% 2.87/1.46  %Foreground sorts:
% 2.87/1.46  
% 2.87/1.46  
% 2.87/1.46  %Background operators:
% 2.87/1.46  
% 2.87/1.46  
% 2.87/1.46  %Foreground operators:
% 2.87/1.46  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.87/1.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.87/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.87/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.87/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.87/1.46  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.87/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.87/1.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.87/1.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.87/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.87/1.46  tff('#skF_5', type, '#skF_5': $i).
% 2.87/1.46  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.87/1.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.87/1.46  tff('#skF_2', type, '#skF_2': $i).
% 2.87/1.46  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.87/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.87/1.46  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.87/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.87/1.46  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.87/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.87/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.87/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.87/1.46  tff('#skF_4', type, '#skF_4': $i).
% 2.87/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.87/1.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.87/1.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.87/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.87/1.46  
% 2.87/1.47  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.87/1.47  tff(f_108, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 2.87/1.47  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.87/1.47  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.87/1.47  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.87/1.47  tff(f_71, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 2.87/1.47  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 2.87/1.47  tff(f_59, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 2.87/1.47  tff(f_48, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.87/1.47  tff(f_41, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, k1_tarski(D))) <=> (r2_hidden(A, C) & (B = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 2.87/1.47  tff(f_35, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 2.87/1.47  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.87/1.47  tff(c_48, plain, (k1_funct_1('#skF_5', '#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.87/1.47  tff(c_50, plain, (r2_hidden('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.87/1.47  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_tarski('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.87/1.47  tff(c_76, plain, (![C_38, A_39, B_40]: (v1_relat_1(C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.87/1.47  tff(c_80, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_76])).
% 2.87/1.47  tff(c_56, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.87/1.47  tff(c_54, plain, (v1_funct_2('#skF_5', '#skF_2', k1_tarski('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.87/1.47  tff(c_120, plain, (![A_61, B_62, C_63]: (k1_relset_1(A_61, B_62, C_63)=k1_relat_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.87/1.47  tff(c_124, plain, (k1_relset_1('#skF_2', k1_tarski('#skF_3'), '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_120])).
% 2.87/1.47  tff(c_180, plain, (![B_92, A_93, C_94]: (k1_xboole_0=B_92 | k1_relset_1(A_93, B_92, C_94)=A_93 | ~v1_funct_2(C_94, A_93, B_92) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_93, B_92))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.87/1.47  tff(c_183, plain, (k1_tarski('#skF_3')=k1_xboole_0 | k1_relset_1('#skF_2', k1_tarski('#skF_3'), '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_52, c_180])).
% 2.87/1.47  tff(c_186, plain, (k1_tarski('#skF_3')=k1_xboole_0 | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_124, c_183])).
% 2.87/1.47  tff(c_187, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(splitLeft, [status(thm)], [c_186])).
% 2.87/1.47  tff(c_30, plain, (![B_24, A_23]: (r2_hidden(k1_funct_1(B_24, A_23), k2_relat_1(B_24)) | ~r2_hidden(A_23, k1_relat_1(B_24)) | ~v1_funct_1(B_24) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.87/1.47  tff(c_28, plain, (![A_22]: (k9_relat_1(A_22, k1_relat_1(A_22))=k2_relat_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.87/1.47  tff(c_143, plain, (![A_76, B_77, C_78]: (r2_hidden(k4_tarski('#skF_1'(A_76, B_77, C_78), A_76), C_78) | ~r2_hidden(A_76, k9_relat_1(C_78, B_77)) | ~v1_relat_1(C_78))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.87/1.47  tff(c_18, plain, (![C_15, A_12, B_13]: (r2_hidden(C_15, A_12) | ~r2_hidden(C_15, B_13) | ~m1_subset_1(B_13, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.87/1.47  tff(c_273, plain, (![A_117, B_118, C_119, A_120]: (r2_hidden(k4_tarski('#skF_1'(A_117, B_118, C_119), A_117), A_120) | ~m1_subset_1(C_119, k1_zfmisc_1(A_120)) | ~r2_hidden(A_117, k9_relat_1(C_119, B_118)) | ~v1_relat_1(C_119))), inference(resolution, [status(thm)], [c_143, c_18])).
% 2.87/1.47  tff(c_14, plain, (![D_11, B_9, A_8, C_10]: (D_11=B_9 | ~r2_hidden(k4_tarski(A_8, B_9), k2_zfmisc_1(C_10, k1_tarski(D_11))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.87/1.47  tff(c_295, plain, (![C_121, B_122, A_123, D_125, C_124]: (D_125=A_123 | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(C_124, k1_tarski(D_125)))) | ~r2_hidden(A_123, k9_relat_1(C_121, B_122)) | ~v1_relat_1(C_121))), inference(resolution, [status(thm)], [c_273, c_14])).
% 2.87/1.47  tff(c_297, plain, (![A_123, B_122]: (A_123='#skF_3' | ~r2_hidden(A_123, k9_relat_1('#skF_5', B_122)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_52, c_295])).
% 2.87/1.47  tff(c_313, plain, (![A_130, B_131]: (A_130='#skF_3' | ~r2_hidden(A_130, k9_relat_1('#skF_5', B_131)))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_297])).
% 2.87/1.47  tff(c_343, plain, (![A_130]: (A_130='#skF_3' | ~r2_hidden(A_130, k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_313])).
% 2.87/1.47  tff(c_352, plain, (![A_132]: (A_132='#skF_3' | ~r2_hidden(A_132, k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_343])).
% 2.87/1.47  tff(c_376, plain, (![A_23]: (k1_funct_1('#skF_5', A_23)='#skF_3' | ~r2_hidden(A_23, k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_30, c_352])).
% 2.87/1.47  tff(c_391, plain, (![A_135]: (k1_funct_1('#skF_5', A_135)='#skF_3' | ~r2_hidden(A_135, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_56, c_187, c_376])).
% 2.87/1.47  tff(c_421, plain, (k1_funct_1('#skF_5', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_50, c_391])).
% 2.87/1.47  tff(c_432, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_421])).
% 2.87/1.47  tff(c_433, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_186])).
% 2.87/1.47  tff(c_10, plain, (![A_7]: (~v1_xboole_0(k1_tarski(A_7)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.87/1.47  tff(c_453, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_433, c_10])).
% 2.87/1.47  tff(c_459, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_453])).
% 2.87/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.47  
% 2.87/1.47  Inference rules
% 2.87/1.47  ----------------------
% 2.87/1.47  #Ref     : 0
% 2.87/1.47  #Sup     : 91
% 2.87/1.47  #Fact    : 0
% 2.87/1.47  #Define  : 0
% 2.87/1.47  #Split   : 1
% 2.87/1.47  #Chain   : 0
% 2.87/1.47  #Close   : 0
% 2.87/1.47  
% 2.87/1.47  Ordering : KBO
% 2.87/1.47  
% 2.87/1.47  Simplification rules
% 2.87/1.47  ----------------------
% 2.87/1.47  #Subsume      : 2
% 2.87/1.47  #Demod        : 18
% 2.87/1.47  #Tautology    : 20
% 2.87/1.47  #SimpNegUnit  : 1
% 2.87/1.47  #BackRed      : 4
% 2.87/1.47  
% 2.87/1.47  #Partial instantiations: 0
% 2.87/1.47  #Strategies tried      : 1
% 2.87/1.47  
% 2.87/1.47  Timing (in seconds)
% 2.87/1.47  ----------------------
% 2.87/1.47  Preprocessing        : 0.36
% 2.87/1.47  Parsing              : 0.19
% 2.87/1.47  CNF conversion       : 0.02
% 2.87/1.47  Main loop            : 0.28
% 2.87/1.47  Inferencing          : 0.11
% 2.87/1.47  Reduction            : 0.08
% 2.87/1.47  Demodulation         : 0.05
% 2.87/1.47  BG Simplification    : 0.02
% 2.87/1.47  Subsumption          : 0.05
% 2.87/1.47  Abstraction          : 0.02
% 2.87/1.47  MUC search           : 0.00
% 2.87/1.47  Cooper               : 0.00
% 2.87/1.47  Total                : 0.68
% 2.87/1.47  Index Insertion      : 0.00
% 2.87/1.47  Index Deletion       : 0.00
% 2.87/1.47  Index Matching       : 0.00
% 2.87/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
