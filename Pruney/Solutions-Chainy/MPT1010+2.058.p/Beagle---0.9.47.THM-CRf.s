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
% DateTime   : Thu Dec  3 10:15:13 EST 2020

% Result     : Theorem 3.01s
% Output     : CNFRefutation 3.01s
% Verified   : 
% Statistics : Number of formulae       :   65 (  88 expanded)
%              Number of leaves         :   36 (  48 expanded)
%              Depth                    :    7
%              Number of atoms          :   94 ( 173 expanded)
%              Number of equality atoms :   30 (  55 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_113,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_102,axiom,(
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

tff(f_71,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,k1_tarski(D)))
    <=> ( r2_hidden(A,C)
        & B = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_76,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_56,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_58,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_60,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_101,plain,(
    ! [C_47,A_48,B_49] :
      ( v1_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_105,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_101])).

tff(c_64,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_62,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_154,plain,(
    ! [A_78,B_79,C_80] :
      ( k1_relset_1(A_78,B_79,C_80) = k1_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_158,plain,(
    k1_relset_1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_154])).

tff(c_430,plain,(
    ! [B_133,A_134,C_135] :
      ( k1_xboole_0 = B_133
      | k1_relset_1(A_134,B_133,C_135) = A_134
      | ~ v1_funct_2(C_135,A_134,B_133)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_134,B_133))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_433,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_relset_1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_60,c_430])).

tff(c_436,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_158,c_433])).

tff(c_437,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_436])).

tff(c_332,plain,(
    ! [B_103,A_104] :
      ( r2_hidden(k4_tarski(B_103,k1_funct_1(A_104,B_103)),A_104)
      | ~ r2_hidden(B_103,k1_relat_1(A_104))
      | ~ v1_funct_1(A_104)
      | ~ v1_relat_1(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_28,plain,(
    ! [C_20,A_17,B_18] :
      ( r2_hidden(C_20,A_17)
      | ~ r2_hidden(C_20,B_18)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_601,plain,(
    ! [B_155,A_156,A_157] :
      ( r2_hidden(k4_tarski(B_155,k1_funct_1(A_156,B_155)),A_157)
      | ~ m1_subset_1(A_156,k1_zfmisc_1(A_157))
      | ~ r2_hidden(B_155,k1_relat_1(A_156))
      | ~ v1_funct_1(A_156)
      | ~ v1_relat_1(A_156) ) ),
    inference(resolution,[status(thm)],[c_332,c_28])).

tff(c_24,plain,(
    ! [D_16,B_14,A_13,C_15] :
      ( D_16 = B_14
      | ~ r2_hidden(k4_tarski(A_13,B_14),k2_zfmisc_1(C_15,k1_tarski(D_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_652,plain,(
    ! [A_164,B_165,D_166,C_167] :
      ( k1_funct_1(A_164,B_165) = D_166
      | ~ m1_subset_1(A_164,k1_zfmisc_1(k2_zfmisc_1(C_167,k1_tarski(D_166))))
      | ~ r2_hidden(B_165,k1_relat_1(A_164))
      | ~ v1_funct_1(A_164)
      | ~ v1_relat_1(A_164) ) ),
    inference(resolution,[status(thm)],[c_601,c_24])).

tff(c_654,plain,(
    ! [B_165] :
      ( k1_funct_1('#skF_6',B_165) = '#skF_4'
      | ~ r2_hidden(B_165,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_60,c_652])).

tff(c_658,plain,(
    ! [B_168] :
      ( k1_funct_1('#skF_6',B_168) = '#skF_4'
      | ~ r2_hidden(B_168,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_64,c_437,c_654])).

tff(c_688,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_58,c_658])).

tff(c_699,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_688])).

tff(c_700,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_436])).

tff(c_6,plain,(
    ! [C_6] : r2_hidden(C_6,k1_tarski(C_6)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_76,plain,(
    ! [B_40,A_41] :
      ( ~ r1_tarski(B_40,A_41)
      | ~ r2_hidden(A_41,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_83,plain,(
    ! [C_6] : ~ r1_tarski(k1_tarski(C_6),C_6) ),
    inference(resolution,[status(thm)],[c_6,c_76])).

tff(c_738,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_700,c_83])).

tff(c_749,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_738])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:48:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.01/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/1.49  
% 3.01/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/1.49  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.01/1.49  
% 3.01/1.49  %Foreground sorts:
% 3.01/1.49  
% 3.01/1.49  
% 3.01/1.49  %Background operators:
% 3.01/1.49  
% 3.01/1.49  
% 3.01/1.49  %Foreground operators:
% 3.01/1.49  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.01/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.01/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.01/1.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.01/1.49  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.01/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.01/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.01/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.01/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.01/1.49  tff('#skF_5', type, '#skF_5': $i).
% 3.01/1.49  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.01/1.49  tff('#skF_6', type, '#skF_6': $i).
% 3.01/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.01/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.01/1.49  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.01/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.01/1.49  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.01/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.01/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.01/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.01/1.49  tff('#skF_4', type, '#skF_4': $i).
% 3.01/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.01/1.49  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.01/1.49  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.01/1.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.01/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.01/1.49  
% 3.01/1.50  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.01/1.50  tff(f_113, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 3.01/1.50  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.01/1.50  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.01/1.50  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.01/1.50  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 3.01/1.50  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 3.01/1.50  tff(f_46, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, k1_tarski(D))) <=> (r2_hidden(A, C) & (B = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 3.01/1.50  tff(f_34, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.01/1.50  tff(f_76, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.01/1.50  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.01/1.50  tff(c_56, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.01/1.50  tff(c_58, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.01/1.50  tff(c_60, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.01/1.50  tff(c_101, plain, (![C_47, A_48, B_49]: (v1_relat_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.01/1.50  tff(c_105, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_60, c_101])).
% 3.01/1.50  tff(c_64, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.01/1.50  tff(c_62, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.01/1.50  tff(c_154, plain, (![A_78, B_79, C_80]: (k1_relset_1(A_78, B_79, C_80)=k1_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.01/1.50  tff(c_158, plain, (k1_relset_1('#skF_3', k1_tarski('#skF_4'), '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_60, c_154])).
% 3.01/1.50  tff(c_430, plain, (![B_133, A_134, C_135]: (k1_xboole_0=B_133 | k1_relset_1(A_134, B_133, C_135)=A_134 | ~v1_funct_2(C_135, A_134, B_133) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_134, B_133))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.01/1.50  tff(c_433, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_relset_1('#skF_3', k1_tarski('#skF_4'), '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_60, c_430])).
% 3.01/1.50  tff(c_436, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_158, c_433])).
% 3.01/1.50  tff(c_437, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_436])).
% 3.01/1.50  tff(c_332, plain, (![B_103, A_104]: (r2_hidden(k4_tarski(B_103, k1_funct_1(A_104, B_103)), A_104) | ~r2_hidden(B_103, k1_relat_1(A_104)) | ~v1_funct_1(A_104) | ~v1_relat_1(A_104))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.01/1.50  tff(c_28, plain, (![C_20, A_17, B_18]: (r2_hidden(C_20, A_17) | ~r2_hidden(C_20, B_18) | ~m1_subset_1(B_18, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.01/1.50  tff(c_601, plain, (![B_155, A_156, A_157]: (r2_hidden(k4_tarski(B_155, k1_funct_1(A_156, B_155)), A_157) | ~m1_subset_1(A_156, k1_zfmisc_1(A_157)) | ~r2_hidden(B_155, k1_relat_1(A_156)) | ~v1_funct_1(A_156) | ~v1_relat_1(A_156))), inference(resolution, [status(thm)], [c_332, c_28])).
% 3.01/1.50  tff(c_24, plain, (![D_16, B_14, A_13, C_15]: (D_16=B_14 | ~r2_hidden(k4_tarski(A_13, B_14), k2_zfmisc_1(C_15, k1_tarski(D_16))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.01/1.50  tff(c_652, plain, (![A_164, B_165, D_166, C_167]: (k1_funct_1(A_164, B_165)=D_166 | ~m1_subset_1(A_164, k1_zfmisc_1(k2_zfmisc_1(C_167, k1_tarski(D_166)))) | ~r2_hidden(B_165, k1_relat_1(A_164)) | ~v1_funct_1(A_164) | ~v1_relat_1(A_164))), inference(resolution, [status(thm)], [c_601, c_24])).
% 3.01/1.50  tff(c_654, plain, (![B_165]: (k1_funct_1('#skF_6', B_165)='#skF_4' | ~r2_hidden(B_165, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_60, c_652])).
% 3.01/1.50  tff(c_658, plain, (![B_168]: (k1_funct_1('#skF_6', B_168)='#skF_4' | ~r2_hidden(B_168, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_64, c_437, c_654])).
% 3.01/1.50  tff(c_688, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_58, c_658])).
% 3.01/1.50  tff(c_699, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_688])).
% 3.01/1.50  tff(c_700, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_436])).
% 3.01/1.50  tff(c_6, plain, (![C_6]: (r2_hidden(C_6, k1_tarski(C_6)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.01/1.50  tff(c_76, plain, (![B_40, A_41]: (~r1_tarski(B_40, A_41) | ~r2_hidden(A_41, B_40))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.01/1.50  tff(c_83, plain, (![C_6]: (~r1_tarski(k1_tarski(C_6), C_6))), inference(resolution, [status(thm)], [c_6, c_76])).
% 3.01/1.50  tff(c_738, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_700, c_83])).
% 3.01/1.50  tff(c_749, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_738])).
% 3.01/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/1.50  
% 3.01/1.50  Inference rules
% 3.01/1.50  ----------------------
% 3.01/1.50  #Ref     : 0
% 3.01/1.50  #Sup     : 151
% 3.01/1.50  #Fact    : 0
% 3.01/1.50  #Define  : 0
% 3.01/1.50  #Split   : 4
% 3.01/1.50  #Chain   : 0
% 3.01/1.50  #Close   : 0
% 3.01/1.50  
% 3.01/1.50  Ordering : KBO
% 3.01/1.50  
% 3.01/1.50  Simplification rules
% 3.01/1.50  ----------------------
% 3.01/1.50  #Subsume      : 19
% 3.01/1.50  #Demod        : 61
% 3.01/1.50  #Tautology    : 47
% 3.01/1.50  #SimpNegUnit  : 1
% 3.01/1.50  #BackRed      : 4
% 3.01/1.50  
% 3.01/1.50  #Partial instantiations: 0
% 3.01/1.50  #Strategies tried      : 1
% 3.01/1.50  
% 3.01/1.50  Timing (in seconds)
% 3.01/1.50  ----------------------
% 3.01/1.51  Preprocessing        : 0.33
% 3.01/1.51  Parsing              : 0.17
% 3.01/1.51  CNF conversion       : 0.02
% 3.01/1.51  Main loop            : 0.36
% 3.01/1.51  Inferencing          : 0.13
% 3.01/1.51  Reduction            : 0.10
% 3.01/1.51  Demodulation         : 0.07
% 3.01/1.51  BG Simplification    : 0.02
% 3.01/1.51  Subsumption          : 0.07
% 3.01/1.51  Abstraction          : 0.02
% 3.01/1.51  MUC search           : 0.00
% 3.01/1.51  Cooper               : 0.00
% 3.01/1.51  Total                : 0.72
% 3.01/1.51  Index Insertion      : 0.00
% 3.01/1.51  Index Deletion       : 0.00
% 3.01/1.51  Index Matching       : 0.00
% 3.01/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
