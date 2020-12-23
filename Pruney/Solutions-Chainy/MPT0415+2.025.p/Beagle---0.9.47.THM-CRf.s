%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:48 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   63 (  98 expanded)
%              Number of leaves         :   32 (  47 expanded)
%              Depth                    :   11
%              Number of atoms          :   85 ( 138 expanded)
%              Number of equality atoms :   29 (  63 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k1_enumset1 > k7_setfam_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_93,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ~ ( B != k1_xboole_0
            & k7_setfam_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                <=> r2_hidden(D,C) ) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_subset_1)).

tff(f_29,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_76,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_31,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_78,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_74,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
         => ( C = k7_setfam_1(A,B)
          <=> ! [D] :
                ( m1_subset_1(D,k1_zfmisc_1(A))
               => ( r2_hidden(D,C)
                <=> r2_hidden(k3_subset_1(A,D),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_16,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_244,plain,(
    ! [A_81,B_82,C_83] :
      ( r2_hidden('#skF_1'(A_81,B_82,C_83),B_82)
      | r2_hidden('#skF_1'(A_81,B_82,C_83),C_83)
      | C_83 = B_82
      | ~ m1_subset_1(C_83,k1_zfmisc_1(A_81))
      | ~ m1_subset_1(B_82,k1_zfmisc_1(A_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_44,plain,(
    ! [A_31] : k1_setfam_1(k1_tarski(A_31)) = A_31 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_6,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_95,plain,(
    ! [A_45,B_46] : k1_setfam_1(k2_tarski(A_45,B_46)) = k3_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_104,plain,(
    ! [A_4] : k3_xboole_0(A_4,A_4) = k1_setfam_1(k1_tarski(A_4)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_95])).

tff(c_107,plain,(
    ! [A_4] : k3_xboole_0(A_4,A_4) = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_104])).

tff(c_117,plain,(
    ! [A_48,B_49] : k5_xboole_0(A_48,k3_xboole_0(A_48,B_49)) = k4_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_126,plain,(
    ! [A_4] : k5_xboole_0(A_4,A_4) = k4_xboole_0(A_4,A_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_117])).

tff(c_130,plain,(
    ! [A_50] : k4_xboole_0(A_50,A_50) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_126])).

tff(c_12,plain,(
    ! [C_9,B_8] : ~ r2_hidden(C_9,k4_xboole_0(B_8,k1_tarski(C_9))) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_135,plain,(
    ! [C_9] : ~ r2_hidden(C_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_12])).

tff(c_275,plain,(
    ! [A_81,B_82] :
      ( r2_hidden('#skF_1'(A_81,B_82,k1_xboole_0),B_82)
      | k1_xboole_0 = B_82
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_81))
      | ~ m1_subset_1(B_82,k1_zfmisc_1(A_81)) ) ),
    inference(resolution,[status(thm)],[c_244,c_135])).

tff(c_288,plain,(
    ! [A_81,B_82] :
      ( r2_hidden('#skF_1'(A_81,B_82,k1_xboole_0),B_82)
      | k1_xboole_0 = B_82
      | ~ m1_subset_1(B_82,k1_zfmisc_1(A_81)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_275])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_146,plain,(
    ! [A_55,C_56,B_57] :
      ( m1_subset_1(A_55,C_56)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(C_56))
      | ~ r2_hidden(A_55,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_151,plain,(
    ! [A_55] :
      ( m1_subset_1(A_55,k1_zfmisc_1('#skF_3'))
      | ~ r2_hidden(A_55,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_54,c_146])).

tff(c_50,plain,(
    k7_setfam_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_158,plain,(
    ! [A_61,B_62] :
      ( k7_setfam_1(A_61,k7_setfam_1(A_61,B_62)) = B_62
      | ~ m1_subset_1(B_62,k1_zfmisc_1(k1_zfmisc_1(A_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_160,plain,(
    k7_setfam_1('#skF_3',k7_setfam_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_54,c_158])).

tff(c_165,plain,(
    k7_setfam_1('#skF_3',k1_xboole_0) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_160])).

tff(c_359,plain,(
    ! [A_96,D_97,B_98] :
      ( r2_hidden(k3_subset_1(A_96,D_97),B_98)
      | ~ r2_hidden(D_97,k7_setfam_1(A_96,B_98))
      | ~ m1_subset_1(D_97,k1_zfmisc_1(A_96))
      | ~ m1_subset_1(k7_setfam_1(A_96,B_98),k1_zfmisc_1(k1_zfmisc_1(A_96)))
      | ~ m1_subset_1(B_98,k1_zfmisc_1(k1_zfmisc_1(A_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_363,plain,(
    ! [D_97] :
      ( r2_hidden(k3_subset_1('#skF_3',D_97),k1_xboole_0)
      | ~ r2_hidden(D_97,k7_setfam_1('#skF_3',k1_xboole_0))
      | ~ m1_subset_1(D_97,k1_zfmisc_1('#skF_3'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3')))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_359])).

tff(c_369,plain,(
    ! [D_97] :
      ( r2_hidden(k3_subset_1('#skF_3',D_97),k1_xboole_0)
      | ~ r2_hidden(D_97,'#skF_4')
      | ~ m1_subset_1(D_97,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_54,c_165,c_363])).

tff(c_373,plain,(
    ! [D_99] :
      ( ~ r2_hidden(D_99,'#skF_4')
      | ~ m1_subset_1(D_99,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_369])).

tff(c_393,plain,(
    ! [A_100] : ~ r2_hidden(A_100,'#skF_4') ),
    inference(resolution,[status(thm)],[c_151,c_373])).

tff(c_397,plain,(
    ! [A_81] :
      ( k1_xboole_0 = '#skF_4'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_81)) ) ),
    inference(resolution,[status(thm)],[c_288,c_393])).

tff(c_412,plain,(
    ! [A_81] : ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_81)) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_397])).

tff(c_419,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_412,c_54])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:52:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.28  
% 2.23/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.28  %$ r2_hidden > m1_subset_1 > k1_enumset1 > k7_setfam_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.23/1.28  
% 2.23/1.28  %Foreground sorts:
% 2.23/1.28  
% 2.23/1.28  
% 2.23/1.28  %Background operators:
% 2.23/1.28  
% 2.23/1.28  
% 2.23/1.28  %Foreground operators:
% 2.23/1.28  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.23/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.23/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.23/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.23/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.23/1.28  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 2.23/1.28  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.23/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.23/1.28  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.23/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.23/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.23/1.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.23/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.23/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.23/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.23/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.23/1.28  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.23/1.28  
% 2.23/1.30  tff(f_93, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_setfam_1)).
% 2.23/1.30  tff(f_42, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.23/1.30  tff(f_56, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) <=> r2_hidden(D, C)))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_subset_1)).
% 2.23/1.30  tff(f_29, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.23/1.30  tff(f_76, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 2.23/1.30  tff(f_31, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.23/1.30  tff(f_78, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.23/1.30  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.23/1.30  tff(f_40, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.23/1.30  tff(f_84, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.23/1.30  tff(f_74, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 2.23/1.30  tff(f_70, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((C = k7_setfam_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, C) <=> r2_hidden(k3_subset_1(A, D), B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_setfam_1)).
% 2.23/1.30  tff(c_52, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.23/1.30  tff(c_16, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.23/1.30  tff(c_244, plain, (![A_81, B_82, C_83]: (r2_hidden('#skF_1'(A_81, B_82, C_83), B_82) | r2_hidden('#skF_1'(A_81, B_82, C_83), C_83) | C_83=B_82 | ~m1_subset_1(C_83, k1_zfmisc_1(A_81)) | ~m1_subset_1(B_82, k1_zfmisc_1(A_81)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.23/1.30  tff(c_4, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.23/1.30  tff(c_44, plain, (![A_31]: (k1_setfam_1(k1_tarski(A_31))=A_31)), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.23/1.30  tff(c_6, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.23/1.30  tff(c_95, plain, (![A_45, B_46]: (k1_setfam_1(k2_tarski(A_45, B_46))=k3_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.23/1.30  tff(c_104, plain, (![A_4]: (k3_xboole_0(A_4, A_4)=k1_setfam_1(k1_tarski(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_95])).
% 2.23/1.30  tff(c_107, plain, (![A_4]: (k3_xboole_0(A_4, A_4)=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_104])).
% 2.23/1.30  tff(c_117, plain, (![A_48, B_49]: (k5_xboole_0(A_48, k3_xboole_0(A_48, B_49))=k4_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.23/1.30  tff(c_126, plain, (![A_4]: (k5_xboole_0(A_4, A_4)=k4_xboole_0(A_4, A_4))), inference(superposition, [status(thm), theory('equality')], [c_107, c_117])).
% 2.23/1.30  tff(c_130, plain, (![A_50]: (k4_xboole_0(A_50, A_50)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_126])).
% 2.23/1.30  tff(c_12, plain, (![C_9, B_8]: (~r2_hidden(C_9, k4_xboole_0(B_8, k1_tarski(C_9))))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.23/1.30  tff(c_135, plain, (![C_9]: (~r2_hidden(C_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_130, c_12])).
% 2.23/1.30  tff(c_275, plain, (![A_81, B_82]: (r2_hidden('#skF_1'(A_81, B_82, k1_xboole_0), B_82) | k1_xboole_0=B_82 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_81)) | ~m1_subset_1(B_82, k1_zfmisc_1(A_81)))), inference(resolution, [status(thm)], [c_244, c_135])).
% 2.23/1.30  tff(c_288, plain, (![A_81, B_82]: (r2_hidden('#skF_1'(A_81, B_82, k1_xboole_0), B_82) | k1_xboole_0=B_82 | ~m1_subset_1(B_82, k1_zfmisc_1(A_81)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_275])).
% 2.23/1.30  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.23/1.30  tff(c_146, plain, (![A_55, C_56, B_57]: (m1_subset_1(A_55, C_56) | ~m1_subset_1(B_57, k1_zfmisc_1(C_56)) | ~r2_hidden(A_55, B_57))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.23/1.30  tff(c_151, plain, (![A_55]: (m1_subset_1(A_55, k1_zfmisc_1('#skF_3')) | ~r2_hidden(A_55, '#skF_4'))), inference(resolution, [status(thm)], [c_54, c_146])).
% 2.23/1.30  tff(c_50, plain, (k7_setfam_1('#skF_3', '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.23/1.30  tff(c_158, plain, (![A_61, B_62]: (k7_setfam_1(A_61, k7_setfam_1(A_61, B_62))=B_62 | ~m1_subset_1(B_62, k1_zfmisc_1(k1_zfmisc_1(A_61))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.23/1.30  tff(c_160, plain, (k7_setfam_1('#skF_3', k7_setfam_1('#skF_3', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_54, c_158])).
% 2.23/1.30  tff(c_165, plain, (k7_setfam_1('#skF_3', k1_xboole_0)='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_160])).
% 2.23/1.30  tff(c_359, plain, (![A_96, D_97, B_98]: (r2_hidden(k3_subset_1(A_96, D_97), B_98) | ~r2_hidden(D_97, k7_setfam_1(A_96, B_98)) | ~m1_subset_1(D_97, k1_zfmisc_1(A_96)) | ~m1_subset_1(k7_setfam_1(A_96, B_98), k1_zfmisc_1(k1_zfmisc_1(A_96))) | ~m1_subset_1(B_98, k1_zfmisc_1(k1_zfmisc_1(A_96))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.23/1.30  tff(c_363, plain, (![D_97]: (r2_hidden(k3_subset_1('#skF_3', D_97), k1_xboole_0) | ~r2_hidden(D_97, k7_setfam_1('#skF_3', k1_xboole_0)) | ~m1_subset_1(D_97, k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_165, c_359])).
% 2.23/1.30  tff(c_369, plain, (![D_97]: (r2_hidden(k3_subset_1('#skF_3', D_97), k1_xboole_0) | ~r2_hidden(D_97, '#skF_4') | ~m1_subset_1(D_97, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_54, c_165, c_363])).
% 2.23/1.30  tff(c_373, plain, (![D_99]: (~r2_hidden(D_99, '#skF_4') | ~m1_subset_1(D_99, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_135, c_369])).
% 2.23/1.30  tff(c_393, plain, (![A_100]: (~r2_hidden(A_100, '#skF_4'))), inference(resolution, [status(thm)], [c_151, c_373])).
% 2.23/1.30  tff(c_397, plain, (![A_81]: (k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_81)))), inference(resolution, [status(thm)], [c_288, c_393])).
% 2.23/1.30  tff(c_412, plain, (![A_81]: (~m1_subset_1('#skF_4', k1_zfmisc_1(A_81)))), inference(negUnitSimplification, [status(thm)], [c_52, c_397])).
% 2.23/1.30  tff(c_419, plain, $false, inference(negUnitSimplification, [status(thm)], [c_412, c_54])).
% 2.23/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.30  
% 2.23/1.30  Inference rules
% 2.23/1.30  ----------------------
% 2.23/1.30  #Ref     : 0
% 2.23/1.30  #Sup     : 74
% 2.23/1.30  #Fact    : 2
% 2.23/1.30  #Define  : 0
% 2.23/1.30  #Split   : 0
% 2.23/1.30  #Chain   : 0
% 2.23/1.30  #Close   : 0
% 2.23/1.30  
% 2.23/1.30  Ordering : KBO
% 2.23/1.30  
% 2.23/1.30  Simplification rules
% 2.23/1.30  ----------------------
% 2.23/1.30  #Subsume      : 15
% 2.23/1.30  #Demod        : 18
% 2.23/1.30  #Tautology    : 34
% 2.23/1.30  #SimpNegUnit  : 5
% 2.23/1.30  #BackRed      : 1
% 2.23/1.30  
% 2.23/1.30  #Partial instantiations: 0
% 2.23/1.30  #Strategies tried      : 1
% 2.23/1.30  
% 2.23/1.30  Timing (in seconds)
% 2.23/1.30  ----------------------
% 2.23/1.30  Preprocessing        : 0.32
% 2.23/1.30  Parsing              : 0.17
% 2.23/1.30  CNF conversion       : 0.02
% 2.23/1.30  Main loop            : 0.23
% 2.23/1.30  Inferencing          : 0.08
% 2.23/1.30  Reduction            : 0.07
% 2.23/1.30  Demodulation         : 0.05
% 2.23/1.30  BG Simplification    : 0.02
% 2.23/1.30  Subsumption          : 0.04
% 2.23/1.30  Abstraction          : 0.01
% 2.23/1.30  MUC search           : 0.00
% 2.23/1.30  Cooper               : 0.00
% 2.23/1.30  Total                : 0.58
% 2.23/1.30  Index Insertion      : 0.00
% 2.23/1.30  Index Deletion       : 0.00
% 2.23/1.30  Index Matching       : 0.00
% 2.23/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
