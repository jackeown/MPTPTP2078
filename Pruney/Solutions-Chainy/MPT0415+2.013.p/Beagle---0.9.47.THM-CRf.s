%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:47 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 101 expanded)
%              Number of leaves         :   34 (  48 expanded)
%              Depth                    :   10
%              Number of atoms          :   97 ( 144 expanded)
%              Number of equality atoms :   34 (  62 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k1_enumset1 > k7_setfam_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(f_51,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_102,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ~ ( B != k1_xboole_0
            & k7_setfam_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_setfam_1)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_53,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_67,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ! [C] :
              ( m1_subset_1(C,A)
             => ( ~ r2_hidden(C,B)
               => r2_hidden(C,k3_subset_1(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_subset_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_85,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
         => ( C = k7_setfam_1(A,B)
          <=> ! [D] :
                ( m1_subset_1(D,k1_zfmisc_1(A))
               => ( r2_hidden(D,C)
                <=> r2_hidden(k3_subset_1(A,D),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_setfam_1)).

tff(c_22,plain,(
    ! [A_15] : m1_subset_1('#skF_1'(A_15),A_15) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_10,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_130,plain,(
    ! [A_55,B_56] : k5_xboole_0(A_55,k3_xboole_0(A_55,B_56)) = k4_xboole_0(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_139,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_130])).

tff(c_147,plain,(
    ! [A_57] : k4_xboole_0(A_57,A_57) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_139])).

tff(c_16,plain,(
    ! [C_12,B_11] : ~ r2_hidden(C_12,k4_xboole_0(B_11,k1_tarski(C_12))) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_152,plain,(
    ! [C_12] : ~ r2_hidden(C_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_16])).

tff(c_24,plain,(
    ! [A_17] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_8,plain,(
    ! [A_6] : k5_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_142,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = k4_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_130])).

tff(c_146,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_142])).

tff(c_182,plain,(
    ! [A_63,B_64] :
      ( k4_xboole_0(A_63,B_64) = k3_subset_1(A_63,B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_192,plain,(
    ! [A_17] : k4_xboole_0(A_17,k1_xboole_0) = k3_subset_1(A_17,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_24,c_182])).

tff(c_196,plain,(
    ! [A_17] : k3_subset_1(A_17,k1_xboole_0) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_192])).

tff(c_302,plain,(
    ! [C_88,A_89,B_90] :
      ( r2_hidden(C_88,k3_subset_1(A_89,B_90))
      | r2_hidden(C_88,B_90)
      | ~ m1_subset_1(C_88,A_89)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(A_89))
      | k1_xboole_0 = A_89 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_307,plain,(
    ! [C_88,A_17] :
      ( r2_hidden(C_88,A_17)
      | r2_hidden(C_88,k1_xboole_0)
      | ~ m1_subset_1(C_88,A_17)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_17))
      | k1_xboole_0 = A_17 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_302])).

tff(c_310,plain,(
    ! [C_88,A_17] :
      ( r2_hidden(C_88,A_17)
      | r2_hidden(C_88,k1_xboole_0)
      | ~ m1_subset_1(C_88,A_17)
      | k1_xboole_0 = A_17 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_307])).

tff(c_311,plain,(
    ! [C_88,A_17] :
      ( r2_hidden(C_88,A_17)
      | ~ m1_subset_1(C_88,A_17)
      | k1_xboole_0 = A_17 ) ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_310])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_210,plain,(
    ! [A_66,C_67,B_68] :
      ( m1_subset_1(A_66,C_67)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(C_67))
      | ~ r2_hidden(A_66,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_218,plain,(
    ! [A_66] :
      ( m1_subset_1(A_66,k1_zfmisc_1('#skF_3'))
      | ~ r2_hidden(A_66,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_52,c_210])).

tff(c_48,plain,(
    k7_setfam_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_232,plain,(
    ! [A_75,B_76] :
      ( k7_setfam_1(A_75,k7_setfam_1(A_75,B_76)) = B_76
      | ~ m1_subset_1(B_76,k1_zfmisc_1(k1_zfmisc_1(A_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_234,plain,(
    k7_setfam_1('#skF_3',k7_setfam_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_52,c_232])).

tff(c_242,plain,(
    k7_setfam_1('#skF_3',k1_xboole_0) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_234])).

tff(c_441,plain,(
    ! [A_108,D_109,B_110] :
      ( r2_hidden(k3_subset_1(A_108,D_109),B_110)
      | ~ r2_hidden(D_109,k7_setfam_1(A_108,B_110))
      | ~ m1_subset_1(D_109,k1_zfmisc_1(A_108))
      | ~ m1_subset_1(k7_setfam_1(A_108,B_110),k1_zfmisc_1(k1_zfmisc_1(A_108)))
      | ~ m1_subset_1(B_110,k1_zfmisc_1(k1_zfmisc_1(A_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_447,plain,(
    ! [D_109] :
      ( r2_hidden(k3_subset_1('#skF_3',D_109),k1_xboole_0)
      | ~ r2_hidden(D_109,k7_setfam_1('#skF_3',k1_xboole_0))
      | ~ m1_subset_1(D_109,k1_zfmisc_1('#skF_3'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3')))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_441])).

tff(c_455,plain,(
    ! [D_109] :
      ( r2_hidden(k3_subset_1('#skF_3',D_109),k1_xboole_0)
      | ~ r2_hidden(D_109,'#skF_4')
      | ~ m1_subset_1(D_109,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_52,c_242,c_447])).

tff(c_459,plain,(
    ! [D_111] :
      ( ~ r2_hidden(D_111,'#skF_4')
      | ~ m1_subset_1(D_111,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_455])).

tff(c_479,plain,(
    ! [A_112] : ~ r2_hidden(A_112,'#skF_4') ),
    inference(resolution,[status(thm)],[c_218,c_459])).

tff(c_483,plain,(
    ! [C_88] :
      ( ~ m1_subset_1(C_88,'#skF_4')
      | k1_xboole_0 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_311,c_479])).

tff(c_487,plain,(
    ! [C_113] : ~ m1_subset_1(C_113,'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_483])).

tff(c_492,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_22,c_487])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:06:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.36/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.33  
% 2.36/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.33  %$ r2_hidden > m1_subset_1 > k1_enumset1 > k7_setfam_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.36/1.33  
% 2.36/1.33  %Foreground sorts:
% 2.36/1.33  
% 2.36/1.33  
% 2.36/1.33  %Background operators:
% 2.36/1.33  
% 2.36/1.33  
% 2.36/1.33  %Foreground operators:
% 2.36/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.36/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.36/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.36/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.36/1.33  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.36/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.36/1.33  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 2.36/1.33  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.36/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.36/1.33  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.36/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.36/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.36/1.33  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.36/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.36/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.36/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.36/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.36/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.36/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.36/1.33  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.36/1.33  
% 2.36/1.35  tff(f_51, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 2.36/1.35  tff(f_102, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_setfam_1)).
% 2.36/1.35  tff(f_35, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.36/1.35  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.36/1.35  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.36/1.35  tff(f_44, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.36/1.35  tff(f_53, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.36/1.35  tff(f_33, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.36/1.35  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.36/1.35  tff(f_48, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.36/1.35  tff(f_67, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, A) => (~r2_hidden(C, B) => r2_hidden(C, k3_subset_1(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_subset_1)).
% 2.36/1.35  tff(f_93, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.36/1.35  tff(f_85, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 2.36/1.35  tff(f_81, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((C = k7_setfam_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, C) <=> r2_hidden(k3_subset_1(A, D), B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_setfam_1)).
% 2.36/1.35  tff(c_22, plain, (![A_15]: (m1_subset_1('#skF_1'(A_15), A_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.36/1.35  tff(c_50, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.36/1.35  tff(c_10, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.36/1.35  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.36/1.35  tff(c_130, plain, (![A_55, B_56]: (k5_xboole_0(A_55, k3_xboole_0(A_55, B_56))=k4_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.36/1.35  tff(c_139, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_130])).
% 2.36/1.35  tff(c_147, plain, (![A_57]: (k4_xboole_0(A_57, A_57)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_139])).
% 2.36/1.35  tff(c_16, plain, (![C_12, B_11]: (~r2_hidden(C_12, k4_xboole_0(B_11, k1_tarski(C_12))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.36/1.35  tff(c_152, plain, (![C_12]: (~r2_hidden(C_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_147, c_16])).
% 2.36/1.35  tff(c_24, plain, (![A_17]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.36/1.35  tff(c_8, plain, (![A_6]: (k5_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.36/1.35  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.36/1.35  tff(c_142, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=k4_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_130])).
% 2.36/1.35  tff(c_146, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_142])).
% 2.36/1.35  tff(c_182, plain, (![A_63, B_64]: (k4_xboole_0(A_63, B_64)=k3_subset_1(A_63, B_64) | ~m1_subset_1(B_64, k1_zfmisc_1(A_63)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.36/1.35  tff(c_192, plain, (![A_17]: (k4_xboole_0(A_17, k1_xboole_0)=k3_subset_1(A_17, k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_182])).
% 2.36/1.35  tff(c_196, plain, (![A_17]: (k3_subset_1(A_17, k1_xboole_0)=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_146, c_192])).
% 2.36/1.35  tff(c_302, plain, (![C_88, A_89, B_90]: (r2_hidden(C_88, k3_subset_1(A_89, B_90)) | r2_hidden(C_88, B_90) | ~m1_subset_1(C_88, A_89) | ~m1_subset_1(B_90, k1_zfmisc_1(A_89)) | k1_xboole_0=A_89)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.36/1.35  tff(c_307, plain, (![C_88, A_17]: (r2_hidden(C_88, A_17) | r2_hidden(C_88, k1_xboole_0) | ~m1_subset_1(C_88, A_17) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_17)) | k1_xboole_0=A_17)), inference(superposition, [status(thm), theory('equality')], [c_196, c_302])).
% 2.36/1.35  tff(c_310, plain, (![C_88, A_17]: (r2_hidden(C_88, A_17) | r2_hidden(C_88, k1_xboole_0) | ~m1_subset_1(C_88, A_17) | k1_xboole_0=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_307])).
% 2.36/1.35  tff(c_311, plain, (![C_88, A_17]: (r2_hidden(C_88, A_17) | ~m1_subset_1(C_88, A_17) | k1_xboole_0=A_17)), inference(negUnitSimplification, [status(thm)], [c_152, c_310])).
% 2.36/1.35  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.36/1.35  tff(c_210, plain, (![A_66, C_67, B_68]: (m1_subset_1(A_66, C_67) | ~m1_subset_1(B_68, k1_zfmisc_1(C_67)) | ~r2_hidden(A_66, B_68))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.36/1.35  tff(c_218, plain, (![A_66]: (m1_subset_1(A_66, k1_zfmisc_1('#skF_3')) | ~r2_hidden(A_66, '#skF_4'))), inference(resolution, [status(thm)], [c_52, c_210])).
% 2.36/1.35  tff(c_48, plain, (k7_setfam_1('#skF_3', '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.36/1.35  tff(c_232, plain, (![A_75, B_76]: (k7_setfam_1(A_75, k7_setfam_1(A_75, B_76))=B_76 | ~m1_subset_1(B_76, k1_zfmisc_1(k1_zfmisc_1(A_75))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.36/1.35  tff(c_234, plain, (k7_setfam_1('#skF_3', k7_setfam_1('#skF_3', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_52, c_232])).
% 2.36/1.35  tff(c_242, plain, (k7_setfam_1('#skF_3', k1_xboole_0)='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_234])).
% 2.36/1.35  tff(c_441, plain, (![A_108, D_109, B_110]: (r2_hidden(k3_subset_1(A_108, D_109), B_110) | ~r2_hidden(D_109, k7_setfam_1(A_108, B_110)) | ~m1_subset_1(D_109, k1_zfmisc_1(A_108)) | ~m1_subset_1(k7_setfam_1(A_108, B_110), k1_zfmisc_1(k1_zfmisc_1(A_108))) | ~m1_subset_1(B_110, k1_zfmisc_1(k1_zfmisc_1(A_108))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.36/1.35  tff(c_447, plain, (![D_109]: (r2_hidden(k3_subset_1('#skF_3', D_109), k1_xboole_0) | ~r2_hidden(D_109, k7_setfam_1('#skF_3', k1_xboole_0)) | ~m1_subset_1(D_109, k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_242, c_441])).
% 2.36/1.35  tff(c_455, plain, (![D_109]: (r2_hidden(k3_subset_1('#skF_3', D_109), k1_xboole_0) | ~r2_hidden(D_109, '#skF_4') | ~m1_subset_1(D_109, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_52, c_242, c_447])).
% 2.36/1.35  tff(c_459, plain, (![D_111]: (~r2_hidden(D_111, '#skF_4') | ~m1_subset_1(D_111, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_152, c_455])).
% 2.36/1.35  tff(c_479, plain, (![A_112]: (~r2_hidden(A_112, '#skF_4'))), inference(resolution, [status(thm)], [c_218, c_459])).
% 2.36/1.35  tff(c_483, plain, (![C_88]: (~m1_subset_1(C_88, '#skF_4') | k1_xboole_0='#skF_4')), inference(resolution, [status(thm)], [c_311, c_479])).
% 2.36/1.35  tff(c_487, plain, (![C_113]: (~m1_subset_1(C_113, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_50, c_483])).
% 2.36/1.35  tff(c_492, plain, $false, inference(resolution, [status(thm)], [c_22, c_487])).
% 2.36/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.35  
% 2.36/1.35  Inference rules
% 2.36/1.35  ----------------------
% 2.36/1.35  #Ref     : 0
% 2.36/1.35  #Sup     : 100
% 2.36/1.35  #Fact    : 0
% 2.36/1.35  #Define  : 0
% 2.36/1.35  #Split   : 0
% 2.36/1.35  #Chain   : 0
% 2.36/1.35  #Close   : 0
% 2.36/1.35  
% 2.36/1.35  Ordering : KBO
% 2.36/1.35  
% 2.36/1.35  Simplification rules
% 2.36/1.35  ----------------------
% 2.36/1.35  #Subsume      : 16
% 2.36/1.35  #Demod        : 17
% 2.36/1.35  #Tautology    : 50
% 2.36/1.35  #SimpNegUnit  : 7
% 2.36/1.35  #BackRed      : 0
% 2.36/1.35  
% 2.36/1.35  #Partial instantiations: 0
% 2.36/1.35  #Strategies tried      : 1
% 2.36/1.35  
% 2.36/1.35  Timing (in seconds)
% 2.36/1.35  ----------------------
% 2.68/1.35  Preprocessing        : 0.33
% 2.68/1.35  Parsing              : 0.18
% 2.68/1.35  CNF conversion       : 0.02
% 2.68/1.35  Main loop            : 0.26
% 2.68/1.35  Inferencing          : 0.10
% 2.68/1.35  Reduction            : 0.08
% 2.68/1.35  Demodulation         : 0.05
% 2.68/1.35  BG Simplification    : 0.02
% 2.68/1.35  Subsumption          : 0.04
% 2.68/1.35  Abstraction          : 0.01
% 2.68/1.35  MUC search           : 0.00
% 2.68/1.35  Cooper               : 0.00
% 2.68/1.35  Total                : 0.62
% 2.68/1.35  Index Insertion      : 0.00
% 2.68/1.35  Index Deletion       : 0.00
% 2.68/1.35  Index Matching       : 0.00
% 2.68/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
