%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:18 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :   71 (  95 expanded)
%              Number of leaves         :   39 (  52 expanded)
%              Depth                    :    9
%              Number of atoms          :   94 ( 176 expanded)
%              Number of equality atoms :   27 (  54 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

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
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_58,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

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

tff(f_69,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_74,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_66,plain,(
    k1_funct_1('#skF_8','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_70,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_159,plain,(
    ! [C_64,B_65,A_66] :
      ( v5_relat_1(C_64,B_65)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_66,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_163,plain,(
    v5_relat_1('#skF_8',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_70,c_159])).

tff(c_68,plain,(
    r2_hidden('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_42,plain,(
    ! [A_22,B_23] : v1_relat_1(k2_zfmisc_1(A_22,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_138,plain,(
    ! [B_59,A_60] :
      ( v1_relat_1(B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_60))
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_141,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))) ),
    inference(resolution,[status(thm)],[c_70,c_138])).

tff(c_144,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_141])).

tff(c_74,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_72,plain,(
    v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_196,plain,(
    ! [A_80,B_81,C_82] :
      ( k1_relset_1(A_80,B_81,C_82) = k1_relat_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_200,plain,(
    k1_relset_1('#skF_5',k1_tarski('#skF_6'),'#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_70,c_196])).

tff(c_399,plain,(
    ! [B_118,A_119,C_120] :
      ( k1_xboole_0 = B_118
      | k1_relset_1(A_119,B_118,C_120) = A_119
      | ~ v1_funct_2(C_120,A_119,B_118)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_119,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_402,plain,
    ( k1_tarski('#skF_6') = k1_xboole_0
    | k1_relset_1('#skF_5',k1_tarski('#skF_6'),'#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_70,c_399])).

tff(c_405,plain,
    ( k1_tarski('#skF_6') = k1_xboole_0
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_200,c_402])).

tff(c_406,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_405])).

tff(c_361,plain,(
    ! [B_110,C_111,A_112] :
      ( r2_hidden(k1_funct_1(B_110,C_111),A_112)
      | ~ r2_hidden(C_111,k1_relat_1(B_110))
      | ~ v1_funct_1(B_110)
      | ~ v5_relat_1(B_110,A_112)
      | ~ v1_relat_1(B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_4,plain,(
    ! [C_6,A_2] :
      ( C_6 = A_2
      | ~ r2_hidden(C_6,k1_tarski(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_379,plain,(
    ! [B_110,C_111,A_2] :
      ( k1_funct_1(B_110,C_111) = A_2
      | ~ r2_hidden(C_111,k1_relat_1(B_110))
      | ~ v1_funct_1(B_110)
      | ~ v5_relat_1(B_110,k1_tarski(A_2))
      | ~ v1_relat_1(B_110) ) ),
    inference(resolution,[status(thm)],[c_361,c_4])).

tff(c_410,plain,(
    ! [C_111,A_2] :
      ( k1_funct_1('#skF_8',C_111) = A_2
      | ~ r2_hidden(C_111,'#skF_5')
      | ~ v1_funct_1('#skF_8')
      | ~ v5_relat_1('#skF_8',k1_tarski(A_2))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_406,c_379])).

tff(c_420,plain,(
    ! [C_121,A_122] :
      ( k1_funct_1('#skF_8',C_121) = A_122
      | ~ r2_hidden(C_121,'#skF_5')
      | ~ v5_relat_1('#skF_8',k1_tarski(A_122)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_74,c_410])).

tff(c_440,plain,(
    ! [A_123] :
      ( k1_funct_1('#skF_8','#skF_7') = A_123
      | ~ v5_relat_1('#skF_8',k1_tarski(A_123)) ) ),
    inference(resolution,[status(thm)],[c_68,c_420])).

tff(c_443,plain,(
    k1_funct_1('#skF_8','#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_163,c_440])).

tff(c_447,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_443])).

tff(c_448,plain,(
    k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_405])).

tff(c_6,plain,(
    ! [C_6] : r2_hidden(C_6,k1_tarski(C_6)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_97,plain,(
    ! [B_48,A_49] :
      ( ~ r1_tarski(B_48,A_49)
      | ~ r2_hidden(A_49,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_112,plain,(
    ! [C_6] : ~ r1_tarski(k1_tarski(C_6),C_6) ),
    inference(resolution,[status(thm)],[c_6,c_97])).

tff(c_469,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_448,c_112])).

tff(c_480,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_469])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:54:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.62/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.37  
% 2.62/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.37  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_1
% 2.62/1.37  
% 2.62/1.37  %Foreground sorts:
% 2.62/1.37  
% 2.62/1.37  
% 2.62/1.37  %Background operators:
% 2.62/1.37  
% 2.62/1.37  
% 2.62/1.37  %Foreground operators:
% 2.62/1.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.62/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.62/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.62/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.62/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.62/1.37  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.62/1.37  tff('#skF_7', type, '#skF_7': $i).
% 2.62/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.62/1.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.62/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.62/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.62/1.37  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.62/1.37  tff('#skF_6', type, '#skF_6': $i).
% 2.62/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.62/1.37  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.62/1.37  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.62/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.62/1.37  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.62/1.37  tff('#skF_8', type, '#skF_8': $i).
% 2.62/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.62/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.62/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.62/1.37  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.62/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.62/1.37  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.62/1.37  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.62/1.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.62/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.62/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.62/1.37  
% 2.62/1.38  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.62/1.38  tff(f_113, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 2.62/1.38  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.62/1.38  tff(f_58, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.62/1.38  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.62/1.38  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.62/1.38  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.62/1.38  tff(f_69, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_1)).
% 2.62/1.38  tff(f_34, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.62/1.38  tff(f_74, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.62/1.38  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.62/1.38  tff(c_66, plain, (k1_funct_1('#skF_8', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.62/1.38  tff(c_70, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.62/1.38  tff(c_159, plain, (![C_64, B_65, A_66]: (v5_relat_1(C_64, B_65) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_66, B_65))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.62/1.38  tff(c_163, plain, (v5_relat_1('#skF_8', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_70, c_159])).
% 2.62/1.38  tff(c_68, plain, (r2_hidden('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.62/1.38  tff(c_42, plain, (![A_22, B_23]: (v1_relat_1(k2_zfmisc_1(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.62/1.38  tff(c_138, plain, (![B_59, A_60]: (v1_relat_1(B_59) | ~m1_subset_1(B_59, k1_zfmisc_1(A_60)) | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.62/1.38  tff(c_141, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))), inference(resolution, [status(thm)], [c_70, c_138])).
% 2.62/1.38  tff(c_144, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_141])).
% 2.62/1.38  tff(c_74, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.62/1.38  tff(c_72, plain, (v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.62/1.38  tff(c_196, plain, (![A_80, B_81, C_82]: (k1_relset_1(A_80, B_81, C_82)=k1_relat_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.62/1.38  tff(c_200, plain, (k1_relset_1('#skF_5', k1_tarski('#skF_6'), '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_70, c_196])).
% 2.62/1.38  tff(c_399, plain, (![B_118, A_119, C_120]: (k1_xboole_0=B_118 | k1_relset_1(A_119, B_118, C_120)=A_119 | ~v1_funct_2(C_120, A_119, B_118) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_119, B_118))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.62/1.38  tff(c_402, plain, (k1_tarski('#skF_6')=k1_xboole_0 | k1_relset_1('#skF_5', k1_tarski('#skF_6'), '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_70, c_399])).
% 2.62/1.38  tff(c_405, plain, (k1_tarski('#skF_6')=k1_xboole_0 | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_200, c_402])).
% 2.62/1.38  tff(c_406, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(splitLeft, [status(thm)], [c_405])).
% 2.62/1.38  tff(c_361, plain, (![B_110, C_111, A_112]: (r2_hidden(k1_funct_1(B_110, C_111), A_112) | ~r2_hidden(C_111, k1_relat_1(B_110)) | ~v1_funct_1(B_110) | ~v5_relat_1(B_110, A_112) | ~v1_relat_1(B_110))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.62/1.38  tff(c_4, plain, (![C_6, A_2]: (C_6=A_2 | ~r2_hidden(C_6, k1_tarski(A_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.62/1.38  tff(c_379, plain, (![B_110, C_111, A_2]: (k1_funct_1(B_110, C_111)=A_2 | ~r2_hidden(C_111, k1_relat_1(B_110)) | ~v1_funct_1(B_110) | ~v5_relat_1(B_110, k1_tarski(A_2)) | ~v1_relat_1(B_110))), inference(resolution, [status(thm)], [c_361, c_4])).
% 2.62/1.38  tff(c_410, plain, (![C_111, A_2]: (k1_funct_1('#skF_8', C_111)=A_2 | ~r2_hidden(C_111, '#skF_5') | ~v1_funct_1('#skF_8') | ~v5_relat_1('#skF_8', k1_tarski(A_2)) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_406, c_379])).
% 2.62/1.38  tff(c_420, plain, (![C_121, A_122]: (k1_funct_1('#skF_8', C_121)=A_122 | ~r2_hidden(C_121, '#skF_5') | ~v5_relat_1('#skF_8', k1_tarski(A_122)))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_74, c_410])).
% 2.62/1.38  tff(c_440, plain, (![A_123]: (k1_funct_1('#skF_8', '#skF_7')=A_123 | ~v5_relat_1('#skF_8', k1_tarski(A_123)))), inference(resolution, [status(thm)], [c_68, c_420])).
% 2.62/1.38  tff(c_443, plain, (k1_funct_1('#skF_8', '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_163, c_440])).
% 2.62/1.38  tff(c_447, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_443])).
% 2.62/1.38  tff(c_448, plain, (k1_tarski('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_405])).
% 2.62/1.38  tff(c_6, plain, (![C_6]: (r2_hidden(C_6, k1_tarski(C_6)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.62/1.38  tff(c_97, plain, (![B_48, A_49]: (~r1_tarski(B_48, A_49) | ~r2_hidden(A_49, B_48))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.62/1.38  tff(c_112, plain, (![C_6]: (~r1_tarski(k1_tarski(C_6), C_6))), inference(resolution, [status(thm)], [c_6, c_97])).
% 2.62/1.38  tff(c_469, plain, (~r1_tarski(k1_xboole_0, '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_448, c_112])).
% 2.62/1.38  tff(c_480, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_469])).
% 2.62/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.38  
% 2.62/1.38  Inference rules
% 2.62/1.38  ----------------------
% 2.62/1.38  #Ref     : 0
% 2.62/1.38  #Sup     : 86
% 2.62/1.38  #Fact    : 0
% 2.62/1.38  #Define  : 0
% 2.62/1.38  #Split   : 1
% 2.62/1.38  #Chain   : 0
% 2.62/1.38  #Close   : 0
% 2.62/1.38  
% 2.62/1.38  Ordering : KBO
% 2.62/1.38  
% 2.62/1.38  Simplification rules
% 2.62/1.38  ----------------------
% 2.62/1.38  #Subsume      : 8
% 2.62/1.38  #Demod        : 39
% 2.62/1.38  #Tautology    : 37
% 2.62/1.38  #SimpNegUnit  : 1
% 2.62/1.38  #BackRed      : 5
% 2.62/1.38  
% 2.62/1.38  #Partial instantiations: 0
% 2.62/1.38  #Strategies tried      : 1
% 2.62/1.38  
% 2.62/1.38  Timing (in seconds)
% 2.62/1.38  ----------------------
% 2.62/1.38  Preprocessing        : 0.33
% 2.62/1.38  Parsing              : 0.17
% 2.62/1.38  CNF conversion       : 0.02
% 2.62/1.38  Main loop            : 0.28
% 2.62/1.38  Inferencing          : 0.10
% 2.62/1.39  Reduction            : 0.08
% 2.62/1.39  Demodulation         : 0.06
% 2.62/1.39  BG Simplification    : 0.02
% 2.62/1.39  Subsumption          : 0.05
% 2.62/1.39  Abstraction          : 0.02
% 2.62/1.39  MUC search           : 0.00
% 2.62/1.39  Cooper               : 0.00
% 2.62/1.39  Total                : 0.63
% 2.62/1.39  Index Insertion      : 0.00
% 2.62/1.39  Index Deletion       : 0.00
% 2.62/1.39  Index Matching       : 0.00
% 2.62/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
