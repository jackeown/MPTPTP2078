%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:19 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :   74 (  97 expanded)
%              Number of leaves         :   39 (  51 expanded)
%              Depth                    :    7
%              Number of atoms          :  105 ( 184 expanded)
%              Number of equality atoms :   34 (  59 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_118,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_70,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_107,axiom,(
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

tff(f_80,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,k1_tarski(D)))
    <=> ( r2_hidden(A,C)
        & B = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).

tff(f_44,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_46,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_42,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_85,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_68,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_70,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_44,plain,(
    ! [A_26,B_27] : v1_relat_1(k2_zfmisc_1(A_26,B_27)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_72,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_148,plain,(
    ! [B_66,A_67] :
      ( v1_relat_1(B_66)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(A_67))
      | ~ v1_relat_1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_151,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_72,c_148])).

tff(c_154,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_151])).

tff(c_76,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_74,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_250,plain,(
    ! [A_118,B_119,C_120] :
      ( k1_relset_1(A_118,B_119,C_120) = k1_relat_1(C_120)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_254,plain,(
    k1_relset_1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_72,c_250])).

tff(c_437,plain,(
    ! [B_157,A_158,C_159] :
      ( k1_xboole_0 = B_157
      | k1_relset_1(A_158,B_157,C_159) = A_158
      | ~ v1_funct_2(C_159,A_158,B_157)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(A_158,B_157))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_440,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_relset_1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_72,c_437])).

tff(c_443,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_254,c_440])).

tff(c_444,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_443])).

tff(c_375,plain,(
    ! [A_141,C_142] :
      ( r2_hidden(k4_tarski(A_141,k1_funct_1(C_142,A_141)),C_142)
      | ~ r2_hidden(A_141,k1_relat_1(C_142))
      | ~ v1_funct_1(C_142)
      | ~ v1_relat_1(C_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_40,plain,(
    ! [C_22,A_19,B_20] :
      ( r2_hidden(C_22,A_19)
      | ~ r2_hidden(C_22,B_20)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_583,plain,(
    ! [A_204,C_205,A_206] :
      ( r2_hidden(k4_tarski(A_204,k1_funct_1(C_205,A_204)),A_206)
      | ~ m1_subset_1(C_205,k1_zfmisc_1(A_206))
      | ~ r2_hidden(A_204,k1_relat_1(C_205))
      | ~ v1_funct_1(C_205)
      | ~ v1_relat_1(C_205) ) ),
    inference(resolution,[status(thm)],[c_375,c_40])).

tff(c_36,plain,(
    ! [D_18,B_16,A_15,C_17] :
      ( D_18 = B_16
      | ~ r2_hidden(k4_tarski(A_15,B_16),k2_zfmisc_1(C_17,k1_tarski(D_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_687,plain,(
    ! [C_233,A_234,D_235,C_236] :
      ( k1_funct_1(C_233,A_234) = D_235
      | ~ m1_subset_1(C_233,k1_zfmisc_1(k2_zfmisc_1(C_236,k1_tarski(D_235))))
      | ~ r2_hidden(A_234,k1_relat_1(C_233))
      | ~ v1_funct_1(C_233)
      | ~ v1_relat_1(C_233) ) ),
    inference(resolution,[status(thm)],[c_583,c_36])).

tff(c_689,plain,(
    ! [A_234] :
      ( k1_funct_1('#skF_6',A_234) = '#skF_4'
      | ~ r2_hidden(A_234,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_72,c_687])).

tff(c_693,plain,(
    ! [A_237] :
      ( k1_funct_1('#skF_6',A_237) = '#skF_4'
      | ~ r2_hidden(A_237,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_76,c_444,c_689])).

tff(c_708,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_70,c_693])).

tff(c_715,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_708])).

tff(c_716,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_443])).

tff(c_28,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_110,plain,(
    ! [A_60,B_61] : k1_enumset1(A_60,A_60,B_61) = k2_tarski(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_8,plain,(
    ! [E_8,A_2,C_4] : r2_hidden(E_8,k1_enumset1(A_2,E_8,C_4)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_134,plain,(
    ! [A_62,B_63] : r2_hidden(A_62,k2_tarski(A_62,B_63)) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_8])).

tff(c_142,plain,(
    ! [A_64] : r2_hidden(A_64,k1_tarski(A_64)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_134])).

tff(c_52,plain,(
    ! [B_32,A_31] :
      ( ~ r1_tarski(B_32,A_31)
      | ~ r2_hidden(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_146,plain,(
    ! [A_64] : ~ r1_tarski(k1_tarski(A_64),A_64) ),
    inference(resolution,[status(thm)],[c_142,c_52])).

tff(c_745,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_716,c_146])).

tff(c_754,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_745])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n006.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 11:39:07 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.14/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.47  
% 3.14/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.47  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 3.14/1.47  
% 3.14/1.47  %Foreground sorts:
% 3.14/1.47  
% 3.14/1.47  
% 3.14/1.47  %Background operators:
% 3.14/1.47  
% 3.14/1.47  
% 3.14/1.47  %Foreground operators:
% 3.14/1.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.14/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.14/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.14/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.14/1.47  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.14/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.14/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.14/1.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.14/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.14/1.47  tff('#skF_5', type, '#skF_5': $i).
% 3.14/1.47  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.14/1.47  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.14/1.47  tff('#skF_6', type, '#skF_6': $i).
% 3.14/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.14/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.14/1.47  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.14/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.14/1.47  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.14/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.14/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.14/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.14/1.47  tff('#skF_4', type, '#skF_4': $i).
% 3.14/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.14/1.47  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.14/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.14/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.14/1.47  
% 3.14/1.48  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.14/1.48  tff(f_118, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 3.14/1.48  tff(f_70, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.14/1.48  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.14/1.48  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.14/1.48  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.14/1.48  tff(f_80, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 3.14/1.48  tff(f_61, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 3.14/1.48  tff(f_54, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, k1_tarski(D))) <=> (r2_hidden(A, C) & (B = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 3.14/1.48  tff(f_44, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.14/1.48  tff(f_46, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.14/1.48  tff(f_42, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 3.14/1.48  tff(f_85, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.14/1.48  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.14/1.48  tff(c_68, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.14/1.48  tff(c_70, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.14/1.48  tff(c_44, plain, (![A_26, B_27]: (v1_relat_1(k2_zfmisc_1(A_26, B_27)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.14/1.48  tff(c_72, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.14/1.48  tff(c_148, plain, (![B_66, A_67]: (v1_relat_1(B_66) | ~m1_subset_1(B_66, k1_zfmisc_1(A_67)) | ~v1_relat_1(A_67))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.14/1.48  tff(c_151, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))), inference(resolution, [status(thm)], [c_72, c_148])).
% 3.14/1.48  tff(c_154, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_151])).
% 3.14/1.48  tff(c_76, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.14/1.48  tff(c_74, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.14/1.48  tff(c_250, plain, (![A_118, B_119, C_120]: (k1_relset_1(A_118, B_119, C_120)=k1_relat_1(C_120) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.14/1.48  tff(c_254, plain, (k1_relset_1('#skF_3', k1_tarski('#skF_4'), '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_72, c_250])).
% 3.14/1.48  tff(c_437, plain, (![B_157, A_158, C_159]: (k1_xboole_0=B_157 | k1_relset_1(A_158, B_157, C_159)=A_158 | ~v1_funct_2(C_159, A_158, B_157) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(A_158, B_157))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.14/1.48  tff(c_440, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_relset_1('#skF_3', k1_tarski('#skF_4'), '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_72, c_437])).
% 3.14/1.48  tff(c_443, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_254, c_440])).
% 3.14/1.48  tff(c_444, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_443])).
% 3.14/1.48  tff(c_375, plain, (![A_141, C_142]: (r2_hidden(k4_tarski(A_141, k1_funct_1(C_142, A_141)), C_142) | ~r2_hidden(A_141, k1_relat_1(C_142)) | ~v1_funct_1(C_142) | ~v1_relat_1(C_142))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.14/1.48  tff(c_40, plain, (![C_22, A_19, B_20]: (r2_hidden(C_22, A_19) | ~r2_hidden(C_22, B_20) | ~m1_subset_1(B_20, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.14/1.48  tff(c_583, plain, (![A_204, C_205, A_206]: (r2_hidden(k4_tarski(A_204, k1_funct_1(C_205, A_204)), A_206) | ~m1_subset_1(C_205, k1_zfmisc_1(A_206)) | ~r2_hidden(A_204, k1_relat_1(C_205)) | ~v1_funct_1(C_205) | ~v1_relat_1(C_205))), inference(resolution, [status(thm)], [c_375, c_40])).
% 3.14/1.48  tff(c_36, plain, (![D_18, B_16, A_15, C_17]: (D_18=B_16 | ~r2_hidden(k4_tarski(A_15, B_16), k2_zfmisc_1(C_17, k1_tarski(D_18))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.14/1.48  tff(c_687, plain, (![C_233, A_234, D_235, C_236]: (k1_funct_1(C_233, A_234)=D_235 | ~m1_subset_1(C_233, k1_zfmisc_1(k2_zfmisc_1(C_236, k1_tarski(D_235)))) | ~r2_hidden(A_234, k1_relat_1(C_233)) | ~v1_funct_1(C_233) | ~v1_relat_1(C_233))), inference(resolution, [status(thm)], [c_583, c_36])).
% 3.14/1.48  tff(c_689, plain, (![A_234]: (k1_funct_1('#skF_6', A_234)='#skF_4' | ~r2_hidden(A_234, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_72, c_687])).
% 3.14/1.48  tff(c_693, plain, (![A_237]: (k1_funct_1('#skF_6', A_237)='#skF_4' | ~r2_hidden(A_237, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_76, c_444, c_689])).
% 3.14/1.48  tff(c_708, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_70, c_693])).
% 3.14/1.48  tff(c_715, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_708])).
% 3.14/1.48  tff(c_716, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_443])).
% 3.14/1.48  tff(c_28, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.14/1.48  tff(c_110, plain, (![A_60, B_61]: (k1_enumset1(A_60, A_60, B_61)=k2_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.14/1.48  tff(c_8, plain, (![E_8, A_2, C_4]: (r2_hidden(E_8, k1_enumset1(A_2, E_8, C_4)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.14/1.48  tff(c_134, plain, (![A_62, B_63]: (r2_hidden(A_62, k2_tarski(A_62, B_63)))), inference(superposition, [status(thm), theory('equality')], [c_110, c_8])).
% 3.14/1.48  tff(c_142, plain, (![A_64]: (r2_hidden(A_64, k1_tarski(A_64)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_134])).
% 3.14/1.48  tff(c_52, plain, (![B_32, A_31]: (~r1_tarski(B_32, A_31) | ~r2_hidden(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.14/1.48  tff(c_146, plain, (![A_64]: (~r1_tarski(k1_tarski(A_64), A_64))), inference(resolution, [status(thm)], [c_142, c_52])).
% 3.14/1.48  tff(c_745, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_716, c_146])).
% 3.14/1.48  tff(c_754, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_745])).
% 3.14/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.48  
% 3.14/1.48  Inference rules
% 3.14/1.48  ----------------------
% 3.14/1.48  #Ref     : 0
% 3.14/1.48  #Sup     : 144
% 3.14/1.48  #Fact    : 0
% 3.14/1.48  #Define  : 0
% 3.14/1.48  #Split   : 3
% 3.14/1.48  #Chain   : 0
% 3.14/1.48  #Close   : 0
% 3.14/1.48  
% 3.14/1.48  Ordering : KBO
% 3.14/1.48  
% 3.14/1.48  Simplification rules
% 3.14/1.48  ----------------------
% 3.14/1.48  #Subsume      : 12
% 3.14/1.48  #Demod        : 26
% 3.14/1.48  #Tautology    : 28
% 3.14/1.48  #SimpNegUnit  : 1
% 3.14/1.48  #BackRed      : 4
% 3.14/1.48  
% 3.14/1.48  #Partial instantiations: 0
% 3.14/1.48  #Strategies tried      : 1
% 3.14/1.48  
% 3.14/1.48  Timing (in seconds)
% 3.14/1.48  ----------------------
% 3.14/1.49  Preprocessing        : 0.33
% 3.14/1.49  Parsing              : 0.17
% 3.14/1.49  CNF conversion       : 0.02
% 3.14/1.49  Main loop            : 0.37
% 3.14/1.49  Inferencing          : 0.14
% 3.14/1.49  Reduction            : 0.11
% 3.14/1.49  Demodulation         : 0.08
% 3.14/1.49  BG Simplification    : 0.02
% 3.14/1.49  Subsumption          : 0.08
% 3.14/1.49  Abstraction          : 0.02
% 3.14/1.49  MUC search           : 0.00
% 3.14/1.49  Cooper               : 0.00
% 3.14/1.49  Total                : 0.74
% 3.14/1.49  Index Insertion      : 0.00
% 3.14/1.49  Index Deletion       : 0.00
% 3.14/1.49  Index Matching       : 0.00
% 3.14/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
