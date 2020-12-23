%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:33 EST 2020

% Result     : Theorem 3.56s
% Output     : CNFRefutation 3.56s
% Verified   : 
% Statistics : Number of formulae       :   61 (  69 expanded)
%              Number of leaves         :   31 (  36 expanded)
%              Depth                    :   13
%              Number of atoms          :   90 ( 108 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_89,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( r1_tarski(B,C)
         => r2_relset_1(B,A,k5_relset_1(B,A,D,C),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_38,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_246,plain,(
    ! [A_94,B_95,D_96] :
      ( r2_relset_1(A_94,B_95,D_96,D_96)
      | ~ m1_subset_1(D_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_253,plain,(
    r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_246])).

tff(c_34,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_50,plain,(
    ! [C_39,A_40,B_41] :
      ( v1_relat_1(C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_59,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_50])).

tff(c_4,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(k2_zfmisc_1(A_1,C_3),k2_zfmisc_1(B_2,C_3))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_6] : ~ v1_xboole_0(k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(k1_zfmisc_1(A_4),k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_138,plain,(
    ! [A_70,C_71,B_72] :
      ( m1_subset_1(A_70,C_71)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(C_71))
      | ~ r2_hidden(A_70,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_313,plain,(
    ! [A_115,B_116,A_117] :
      ( m1_subset_1(A_115,B_116)
      | ~ r2_hidden(A_115,A_117)
      | ~ r1_tarski(A_117,B_116) ) ),
    inference(resolution,[status(thm)],[c_14,c_138])).

tff(c_558,plain,(
    ! [A_196,B_197,B_198] :
      ( m1_subset_1(A_196,B_197)
      | ~ r1_tarski(B_198,B_197)
      | v1_xboole_0(B_198)
      | ~ m1_subset_1(A_196,B_198) ) ),
    inference(resolution,[status(thm)],[c_10,c_313])).

tff(c_564,plain,(
    ! [A_196,B_5,A_4] :
      ( m1_subset_1(A_196,k1_zfmisc_1(B_5))
      | v1_xboole_0(k1_zfmisc_1(A_4))
      | ~ m1_subset_1(A_196,k1_zfmisc_1(A_4))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_558])).

tff(c_891,plain,(
    ! [A_313,B_314,A_315] :
      ( m1_subset_1(A_313,k1_zfmisc_1(B_314))
      | ~ m1_subset_1(A_313,k1_zfmisc_1(A_315))
      | ~ r1_tarski(A_315,B_314) ) ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_564])).

tff(c_900,plain,(
    ! [B_318] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(B_318))
      | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),B_318) ) ),
    inference(resolution,[status(thm)],[c_36,c_891])).

tff(c_911,plain,(
    ! [B_319] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_319,'#skF_1')))
      | ~ r1_tarski('#skF_2',B_319) ) ),
    inference(resolution,[status(thm)],[c_4,c_900])).

tff(c_24,plain,(
    ! [C_21,A_19,B_20] :
      ( v4_relat_1(C_21,A_19)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_942,plain,(
    ! [B_320] :
      ( v4_relat_1('#skF_4',B_320)
      | ~ r1_tarski('#skF_2',B_320) ) ),
    inference(resolution,[status(thm)],[c_911,c_24])).

tff(c_18,plain,(
    ! [B_15,A_14] :
      ( k7_relat_1(B_15,A_14) = B_15
      | ~ v4_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_945,plain,(
    ! [B_320] :
      ( k7_relat_1('#skF_4',B_320) = '#skF_4'
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_2',B_320) ) ),
    inference(resolution,[status(thm)],[c_942,c_18])).

tff(c_949,plain,(
    ! [B_321] :
      ( k7_relat_1('#skF_4',B_321) = '#skF_4'
      | ~ r1_tarski('#skF_2',B_321) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_945])).

tff(c_953,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_34,c_949])).

tff(c_277,plain,(
    ! [A_105,B_106,C_107,D_108] :
      ( k5_relset_1(A_105,B_106,C_107,D_108) = k7_relat_1(C_107,D_108)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_284,plain,(
    ! [D_108] : k5_relset_1('#skF_2','#skF_1','#skF_4',D_108) = k7_relat_1('#skF_4',D_108) ),
    inference(resolution,[status(thm)],[c_36,c_277])).

tff(c_32,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k5_relset_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_285,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_32])).

tff(c_954,plain,(
    ~ r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_953,c_285])).

tff(c_957,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_954])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:15:25 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.56/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.56/1.64  
% 3.56/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.56/1.64  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.56/1.64  
% 3.56/1.64  %Foreground sorts:
% 3.56/1.64  
% 3.56/1.64  
% 3.56/1.64  %Background operators:
% 3.56/1.64  
% 3.56/1.64  
% 3.56/1.64  %Foreground operators:
% 3.56/1.64  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 3.56/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.56/1.64  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.56/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.56/1.64  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.56/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.56/1.64  tff('#skF_2', type, '#skF_2': $i).
% 3.56/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.56/1.64  tff('#skF_1', type, '#skF_1': $i).
% 3.56/1.64  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.56/1.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.56/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.56/1.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.56/1.64  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.56/1.64  tff('#skF_4', type, '#skF_4': $i).
% 3.56/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.56/1.64  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.56/1.64  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.56/1.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.56/1.64  
% 3.56/1.66  tff(f_89, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(B, C) => r2_relset_1(B, A, k5_relset_1(B, A, D, C), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_relset_1)).
% 3.56/1.66  tff(f_82, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.56/1.66  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.56/1.66  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 3.56/1.66  tff(f_38, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.56/1.66  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 3.56/1.66  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.56/1.66  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.56/1.66  tff(f_54, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 3.56/1.66  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.56/1.66  tff(f_60, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.56/1.66  tff(f_74, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 3.56/1.66  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.56/1.66  tff(c_246, plain, (![A_94, B_95, D_96]: (r2_relset_1(A_94, B_95, D_96, D_96) | ~m1_subset_1(D_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.56/1.66  tff(c_253, plain, (r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_36, c_246])).
% 3.56/1.66  tff(c_34, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.56/1.66  tff(c_50, plain, (![C_39, A_40, B_41]: (v1_relat_1(C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.56/1.66  tff(c_59, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_50])).
% 3.56/1.66  tff(c_4, plain, (![A_1, C_3, B_2]: (r1_tarski(k2_zfmisc_1(A_1, C_3), k2_zfmisc_1(B_2, C_3)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.56/1.66  tff(c_8, plain, (![A_6]: (~v1_xboole_0(k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.56/1.66  tff(c_6, plain, (![A_4, B_5]: (r1_tarski(k1_zfmisc_1(A_4), k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.56/1.66  tff(c_10, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.56/1.66  tff(c_14, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.56/1.66  tff(c_138, plain, (![A_70, C_71, B_72]: (m1_subset_1(A_70, C_71) | ~m1_subset_1(B_72, k1_zfmisc_1(C_71)) | ~r2_hidden(A_70, B_72))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.56/1.66  tff(c_313, plain, (![A_115, B_116, A_117]: (m1_subset_1(A_115, B_116) | ~r2_hidden(A_115, A_117) | ~r1_tarski(A_117, B_116))), inference(resolution, [status(thm)], [c_14, c_138])).
% 3.56/1.66  tff(c_558, plain, (![A_196, B_197, B_198]: (m1_subset_1(A_196, B_197) | ~r1_tarski(B_198, B_197) | v1_xboole_0(B_198) | ~m1_subset_1(A_196, B_198))), inference(resolution, [status(thm)], [c_10, c_313])).
% 3.56/1.66  tff(c_564, plain, (![A_196, B_5, A_4]: (m1_subset_1(A_196, k1_zfmisc_1(B_5)) | v1_xboole_0(k1_zfmisc_1(A_4)) | ~m1_subset_1(A_196, k1_zfmisc_1(A_4)) | ~r1_tarski(A_4, B_5))), inference(resolution, [status(thm)], [c_6, c_558])).
% 3.56/1.66  tff(c_891, plain, (![A_313, B_314, A_315]: (m1_subset_1(A_313, k1_zfmisc_1(B_314)) | ~m1_subset_1(A_313, k1_zfmisc_1(A_315)) | ~r1_tarski(A_315, B_314))), inference(negUnitSimplification, [status(thm)], [c_8, c_564])).
% 3.56/1.66  tff(c_900, plain, (![B_318]: (m1_subset_1('#skF_4', k1_zfmisc_1(B_318)) | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), B_318))), inference(resolution, [status(thm)], [c_36, c_891])).
% 3.56/1.66  tff(c_911, plain, (![B_319]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_319, '#skF_1'))) | ~r1_tarski('#skF_2', B_319))), inference(resolution, [status(thm)], [c_4, c_900])).
% 3.56/1.66  tff(c_24, plain, (![C_21, A_19, B_20]: (v4_relat_1(C_21, A_19) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.56/1.66  tff(c_942, plain, (![B_320]: (v4_relat_1('#skF_4', B_320) | ~r1_tarski('#skF_2', B_320))), inference(resolution, [status(thm)], [c_911, c_24])).
% 3.56/1.66  tff(c_18, plain, (![B_15, A_14]: (k7_relat_1(B_15, A_14)=B_15 | ~v4_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.56/1.66  tff(c_945, plain, (![B_320]: (k7_relat_1('#skF_4', B_320)='#skF_4' | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_2', B_320))), inference(resolution, [status(thm)], [c_942, c_18])).
% 3.56/1.66  tff(c_949, plain, (![B_321]: (k7_relat_1('#skF_4', B_321)='#skF_4' | ~r1_tarski('#skF_2', B_321))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_945])).
% 3.56/1.66  tff(c_953, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_34, c_949])).
% 3.56/1.66  tff(c_277, plain, (![A_105, B_106, C_107, D_108]: (k5_relset_1(A_105, B_106, C_107, D_108)=k7_relat_1(C_107, D_108) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.56/1.66  tff(c_284, plain, (![D_108]: (k5_relset_1('#skF_2', '#skF_1', '#skF_4', D_108)=k7_relat_1('#skF_4', D_108))), inference(resolution, [status(thm)], [c_36, c_277])).
% 3.56/1.66  tff(c_32, plain, (~r2_relset_1('#skF_2', '#skF_1', k5_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.56/1.66  tff(c_285, plain, (~r2_relset_1('#skF_2', '#skF_1', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_284, c_32])).
% 3.56/1.66  tff(c_954, plain, (~r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_953, c_285])).
% 3.56/1.66  tff(c_957, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_253, c_954])).
% 3.56/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.56/1.66  
% 3.56/1.66  Inference rules
% 3.56/1.66  ----------------------
% 3.56/1.66  #Ref     : 0
% 3.56/1.66  #Sup     : 230
% 3.56/1.66  #Fact    : 0
% 3.56/1.66  #Define  : 0
% 3.56/1.66  #Split   : 2
% 3.56/1.66  #Chain   : 0
% 3.56/1.66  #Close   : 0
% 3.56/1.66  
% 3.56/1.66  Ordering : KBO
% 3.56/1.66  
% 3.56/1.66  Simplification rules
% 3.56/1.66  ----------------------
% 3.56/1.66  #Subsume      : 0
% 3.56/1.66  #Demod        : 23
% 3.56/1.66  #Tautology    : 27
% 3.56/1.66  #SimpNegUnit  : 1
% 3.56/1.66  #BackRed      : 2
% 3.56/1.66  
% 3.56/1.66  #Partial instantiations: 0
% 3.56/1.66  #Strategies tried      : 1
% 3.56/1.66  
% 3.56/1.66  Timing (in seconds)
% 3.56/1.66  ----------------------
% 3.56/1.66  Preprocessing        : 0.33
% 3.56/1.66  Parsing              : 0.18
% 3.56/1.66  CNF conversion       : 0.02
% 3.56/1.66  Main loop            : 0.51
% 3.56/1.66  Inferencing          : 0.18
% 3.56/1.66  Reduction            : 0.16
% 3.56/1.66  Demodulation         : 0.11
% 3.56/1.66  BG Simplification    : 0.02
% 3.56/1.66  Subsumption          : 0.10
% 3.56/1.66  Abstraction          : 0.02
% 3.56/1.66  MUC search           : 0.00
% 3.56/1.66  Cooper               : 0.00
% 3.56/1.66  Total                : 0.87
% 3.56/1.66  Index Insertion      : 0.00
% 3.56/1.66  Index Deletion       : 0.00
% 3.56/1.66  Index Matching       : 0.00
% 3.56/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
