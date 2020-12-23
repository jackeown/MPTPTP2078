%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:09 EST 2020

% Result     : Theorem 3.07s
% Output     : CNFRefutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :   74 (  98 expanded)
%              Number of leaves         :   40 (  53 expanded)
%              Depth                    :   10
%              Number of atoms          :   99 ( 181 expanded)
%              Number of equality atoms :   27 (  54 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_1

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

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
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v5_relat_1(C,A)
        & v1_funct_1(C) )
     => ( r2_hidden(B,k1_relat_1(C))
       => m1_subset_1(k1_funct_1(C,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_1)).

tff(f_50,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_34,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_71,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_66,plain,(
    k1_funct_1('#skF_8','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_70,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_168,plain,(
    ! [C_68,B_69,A_70] :
      ( v5_relat_1(C_68,B_69)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_70,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_172,plain,(
    v5_relat_1('#skF_8',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_70,c_168])).

tff(c_68,plain,(
    r2_hidden('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_150,plain,(
    ! [C_57,A_58,B_59] :
      ( v1_relat_1(C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_154,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_70,c_150])).

tff(c_74,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_72,plain,(
    v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_215,plain,(
    ! [A_81,B_82,C_83] :
      ( k1_relset_1(A_81,B_82,C_83) = k1_relat_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_219,plain,(
    k1_relset_1('#skF_5',k1_tarski('#skF_6'),'#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_70,c_215])).

tff(c_464,plain,(
    ! [B_128,A_129,C_130] :
      ( k1_xboole_0 = B_128
      | k1_relset_1(A_129,B_128,C_130) = A_129
      | ~ v1_funct_2(C_130,A_129,B_128)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_129,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_467,plain,
    ( k1_tarski('#skF_6') = k1_xboole_0
    | k1_relset_1('#skF_5',k1_tarski('#skF_6'),'#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_70,c_464])).

tff(c_470,plain,
    ( k1_tarski('#skF_6') = k1_xboole_0
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_219,c_467])).

tff(c_471,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_470])).

tff(c_42,plain,(
    ! [C_21,B_20,A_19] :
      ( m1_subset_1(k1_funct_1(C_21,B_20),A_19)
      | ~ r2_hidden(B_20,k1_relat_1(C_21))
      | ~ v1_funct_1(C_21)
      | ~ v5_relat_1(C_21,A_19)
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_475,plain,(
    ! [B_20,A_19] :
      ( m1_subset_1(k1_funct_1('#skF_8',B_20),A_19)
      | ~ r2_hidden(B_20,'#skF_5')
      | ~ v1_funct_1('#skF_8')
      | ~ v5_relat_1('#skF_8',A_19)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_471,c_42])).

tff(c_485,plain,(
    ! [B_131,A_132] :
      ( m1_subset_1(k1_funct_1('#skF_8',B_131),A_132)
      | ~ r2_hidden(B_131,'#skF_5')
      | ~ v5_relat_1('#skF_8',A_132) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_74,c_475])).

tff(c_38,plain,(
    ! [A_16] : ~ v1_xboole_0(k1_tarski(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_138,plain,(
    ! [A_55,B_56] :
      ( r2_hidden(A_55,B_56)
      | v1_xboole_0(B_56)
      | ~ m1_subset_1(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4,plain,(
    ! [C_6,A_2] :
      ( C_6 = A_2
      | ~ r2_hidden(C_6,k1_tarski(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_145,plain,(
    ! [A_55,A_2] :
      ( A_55 = A_2
      | v1_xboole_0(k1_tarski(A_2))
      | ~ m1_subset_1(A_55,k1_tarski(A_2)) ) ),
    inference(resolution,[status(thm)],[c_138,c_4])).

tff(c_149,plain,(
    ! [A_55,A_2] :
      ( A_55 = A_2
      | ~ m1_subset_1(A_55,k1_tarski(A_2)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_145])).

tff(c_542,plain,(
    ! [B_133,A_134] :
      ( k1_funct_1('#skF_8',B_133) = A_134
      | ~ r2_hidden(B_133,'#skF_5')
      | ~ v5_relat_1('#skF_8',k1_tarski(A_134)) ) ),
    inference(resolution,[status(thm)],[c_485,c_149])).

tff(c_562,plain,(
    ! [A_135] :
      ( k1_funct_1('#skF_8','#skF_7') = A_135
      | ~ v5_relat_1('#skF_8',k1_tarski(A_135)) ) ),
    inference(resolution,[status(thm)],[c_68,c_542])).

tff(c_565,plain,(
    k1_funct_1('#skF_8','#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_172,c_562])).

tff(c_569,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_565])).

tff(c_570,plain,(
    k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_470])).

tff(c_6,plain,(
    ! [C_6] : r2_hidden(C_6,k1_tarski(C_6)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_103,plain,(
    ! [B_46,A_47] :
      ( ~ r1_tarski(B_46,A_47)
      | ~ r2_hidden(A_47,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_118,plain,(
    ! [C_6] : ~ r1_tarski(k1_tarski(C_6),C_6) ),
    inference(resolution,[status(thm)],[c_6,c_103])).

tff(c_597,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_570,c_118])).

tff(c_615,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_597])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:13:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.07/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/1.58  
% 3.07/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/1.59  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_1
% 3.07/1.59  
% 3.07/1.59  %Foreground sorts:
% 3.07/1.59  
% 3.07/1.59  
% 3.07/1.59  %Background operators:
% 3.07/1.59  
% 3.07/1.59  
% 3.07/1.59  %Foreground operators:
% 3.07/1.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.07/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.07/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.07/1.59  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.07/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.07/1.59  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.07/1.59  tff('#skF_7', type, '#skF_7': $i).
% 3.07/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.07/1.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.07/1.59  tff('#skF_5', type, '#skF_5': $i).
% 3.07/1.59  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.07/1.59  tff('#skF_6', type, '#skF_6': $i).
% 3.07/1.59  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.07/1.59  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.07/1.59  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.07/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.07/1.59  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.07/1.59  tff('#skF_8', type, '#skF_8': $i).
% 3.07/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.07/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.07/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.07/1.59  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.07/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.07/1.59  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.07/1.59  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.07/1.59  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.07/1.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.07/1.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.07/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.07/1.59  
% 3.07/1.60  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.07/1.60  tff(f_114, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 3.07/1.60  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.07/1.60  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.07/1.60  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.07/1.60  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.07/1.60  tff(f_66, axiom, (![A, B, C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (r2_hidden(B, k1_relat_1(C)) => m1_subset_1(k1_funct_1(C, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t176_funct_1)).
% 3.07/1.60  tff(f_50, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 3.07/1.60  tff(f_56, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.07/1.60  tff(f_34, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 3.07/1.60  tff(f_71, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.07/1.60  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.07/1.60  tff(c_66, plain, (k1_funct_1('#skF_8', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.07/1.60  tff(c_70, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.07/1.60  tff(c_168, plain, (![C_68, B_69, A_70]: (v5_relat_1(C_68, B_69) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_70, B_69))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.07/1.60  tff(c_172, plain, (v5_relat_1('#skF_8', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_70, c_168])).
% 3.07/1.60  tff(c_68, plain, (r2_hidden('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.07/1.60  tff(c_150, plain, (![C_57, A_58, B_59]: (v1_relat_1(C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.07/1.60  tff(c_154, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_70, c_150])).
% 3.07/1.60  tff(c_74, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.07/1.60  tff(c_72, plain, (v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.07/1.60  tff(c_215, plain, (![A_81, B_82, C_83]: (k1_relset_1(A_81, B_82, C_83)=k1_relat_1(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.07/1.60  tff(c_219, plain, (k1_relset_1('#skF_5', k1_tarski('#skF_6'), '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_70, c_215])).
% 3.07/1.60  tff(c_464, plain, (![B_128, A_129, C_130]: (k1_xboole_0=B_128 | k1_relset_1(A_129, B_128, C_130)=A_129 | ~v1_funct_2(C_130, A_129, B_128) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_129, B_128))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.07/1.60  tff(c_467, plain, (k1_tarski('#skF_6')=k1_xboole_0 | k1_relset_1('#skF_5', k1_tarski('#skF_6'), '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_70, c_464])).
% 3.07/1.60  tff(c_470, plain, (k1_tarski('#skF_6')=k1_xboole_0 | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_219, c_467])).
% 3.07/1.60  tff(c_471, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(splitLeft, [status(thm)], [c_470])).
% 3.07/1.60  tff(c_42, plain, (![C_21, B_20, A_19]: (m1_subset_1(k1_funct_1(C_21, B_20), A_19) | ~r2_hidden(B_20, k1_relat_1(C_21)) | ~v1_funct_1(C_21) | ~v5_relat_1(C_21, A_19) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.07/1.60  tff(c_475, plain, (![B_20, A_19]: (m1_subset_1(k1_funct_1('#skF_8', B_20), A_19) | ~r2_hidden(B_20, '#skF_5') | ~v1_funct_1('#skF_8') | ~v5_relat_1('#skF_8', A_19) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_471, c_42])).
% 3.07/1.60  tff(c_485, plain, (![B_131, A_132]: (m1_subset_1(k1_funct_1('#skF_8', B_131), A_132) | ~r2_hidden(B_131, '#skF_5') | ~v5_relat_1('#skF_8', A_132))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_74, c_475])).
% 3.07/1.60  tff(c_38, plain, (![A_16]: (~v1_xboole_0(k1_tarski(A_16)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.07/1.60  tff(c_138, plain, (![A_55, B_56]: (r2_hidden(A_55, B_56) | v1_xboole_0(B_56) | ~m1_subset_1(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.07/1.60  tff(c_4, plain, (![C_6, A_2]: (C_6=A_2 | ~r2_hidden(C_6, k1_tarski(A_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.07/1.60  tff(c_145, plain, (![A_55, A_2]: (A_55=A_2 | v1_xboole_0(k1_tarski(A_2)) | ~m1_subset_1(A_55, k1_tarski(A_2)))), inference(resolution, [status(thm)], [c_138, c_4])).
% 3.07/1.60  tff(c_149, plain, (![A_55, A_2]: (A_55=A_2 | ~m1_subset_1(A_55, k1_tarski(A_2)))), inference(negUnitSimplification, [status(thm)], [c_38, c_145])).
% 3.07/1.60  tff(c_542, plain, (![B_133, A_134]: (k1_funct_1('#skF_8', B_133)=A_134 | ~r2_hidden(B_133, '#skF_5') | ~v5_relat_1('#skF_8', k1_tarski(A_134)))), inference(resolution, [status(thm)], [c_485, c_149])).
% 3.07/1.60  tff(c_562, plain, (![A_135]: (k1_funct_1('#skF_8', '#skF_7')=A_135 | ~v5_relat_1('#skF_8', k1_tarski(A_135)))), inference(resolution, [status(thm)], [c_68, c_542])).
% 3.07/1.60  tff(c_565, plain, (k1_funct_1('#skF_8', '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_172, c_562])).
% 3.07/1.60  tff(c_569, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_565])).
% 3.07/1.60  tff(c_570, plain, (k1_tarski('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_470])).
% 3.07/1.60  tff(c_6, plain, (![C_6]: (r2_hidden(C_6, k1_tarski(C_6)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.07/1.60  tff(c_103, plain, (![B_46, A_47]: (~r1_tarski(B_46, A_47) | ~r2_hidden(A_47, B_46))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.07/1.60  tff(c_118, plain, (![C_6]: (~r1_tarski(k1_tarski(C_6), C_6))), inference(resolution, [status(thm)], [c_6, c_103])).
% 3.07/1.60  tff(c_597, plain, (~r1_tarski(k1_xboole_0, '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_570, c_118])).
% 3.07/1.60  tff(c_615, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_597])).
% 3.07/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/1.60  
% 3.07/1.60  Inference rules
% 3.07/1.60  ----------------------
% 3.07/1.60  #Ref     : 0
% 3.07/1.60  #Sup     : 113
% 3.07/1.60  #Fact    : 0
% 3.07/1.60  #Define  : 0
% 3.07/1.60  #Split   : 4
% 3.07/1.60  #Chain   : 0
% 3.07/1.60  #Close   : 0
% 3.07/1.60  
% 3.07/1.60  Ordering : KBO
% 3.07/1.60  
% 3.07/1.60  Simplification rules
% 3.07/1.60  ----------------------
% 3.07/1.60  #Subsume      : 18
% 3.07/1.60  #Demod        : 49
% 3.07/1.60  #Tautology    : 36
% 3.07/1.60  #SimpNegUnit  : 5
% 3.07/1.60  #BackRed      : 5
% 3.07/1.60  
% 3.07/1.60  #Partial instantiations: 0
% 3.07/1.60  #Strategies tried      : 1
% 3.07/1.60  
% 3.07/1.60  Timing (in seconds)
% 3.07/1.60  ----------------------
% 3.07/1.60  Preprocessing        : 0.42
% 3.07/1.60  Parsing              : 0.20
% 3.07/1.60  CNF conversion       : 0.03
% 3.07/1.60  Main loop            : 0.32
% 3.07/1.60  Inferencing          : 0.11
% 3.07/1.60  Reduction            : 0.10
% 3.07/1.60  Demodulation         : 0.07
% 3.07/1.60  BG Simplification    : 0.02
% 3.07/1.60  Subsumption          : 0.06
% 3.07/1.60  Abstraction          : 0.02
% 3.07/1.60  MUC search           : 0.00
% 3.07/1.60  Cooper               : 0.00
% 3.07/1.60  Total                : 0.77
% 3.07/1.60  Index Insertion      : 0.00
% 3.07/1.60  Index Deletion       : 0.00
% 3.07/1.60  Index Matching       : 0.00
% 3.07/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
