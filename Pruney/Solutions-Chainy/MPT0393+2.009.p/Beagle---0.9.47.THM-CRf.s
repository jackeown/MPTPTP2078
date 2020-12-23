%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:18 EST 2020

% Result     : Theorem 9.53s
% Output     : CNFRefutation 9.66s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 128 expanded)
%              Number of leaves         :   32 (  58 expanded)
%              Depth                    :   11
%              Number of atoms          :   88 ( 204 expanded)
%              Number of equality atoms :   35 ( 100 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_101,negated_conjecture,(
    ~ ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_77,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_68,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(B,C) )
     => ( A = k1_xboole_0
        | r1_tarski(B,k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_79,axiom,(
    ! [A] : r1_tarski(k1_setfam_1(A),k3_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_setfam_1)).

tff(c_78,plain,(
    k1_setfam_1(k1_tarski('#skF_7')) != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_215,plain,(
    ! [A_78,B_79,C_80] :
      ( r2_hidden(A_78,B_79)
      | ~ r2_hidden(A_78,k4_xboole_0(B_79,k1_tarski(C_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_13387,plain,(
    ! [B_33255,C_33256,B_33257] :
      ( r2_hidden('#skF_1'(k4_xboole_0(B_33255,k1_tarski(C_33256)),B_33257),B_33255)
      | r1_tarski(k4_xboole_0(B_33255,k1_tarski(C_33256)),B_33257) ) ),
    inference(resolution,[status(thm)],[c_6,c_215])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_13449,plain,(
    ! [B_33444,C_33445] : r1_tarski(k4_xboole_0(B_33444,k1_tarski(C_33445)),B_33444) ),
    inference(resolution,[status(thm)],[c_13387,c_4])).

tff(c_64,plain,(
    ! [A_30] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_30)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_135,plain,(
    ! [A_64,B_65] :
      ( r1_tarski(A_64,B_65)
      | ~ m1_subset_1(A_64,k1_zfmisc_1(B_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_143,plain,(
    ! [A_30] : r1_tarski(k1_xboole_0,A_30) ),
    inference(resolution,[status(thm)],[c_64,c_135])).

tff(c_169,plain,(
    ! [B_75,A_76] :
      ( B_75 = A_76
      | ~ r1_tarski(B_75,A_76)
      | ~ r1_tarski(A_76,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_178,plain,(
    ! [A_30] :
      ( k1_xboole_0 = A_30
      | ~ r1_tarski(A_30,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_143,c_169])).

tff(c_13477,plain,(
    ! [C_33539] : k4_xboole_0(k1_xboole_0,k1_tarski(C_33539)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_13449,c_178])).

tff(c_60,plain,(
    ! [C_29,B_28] : ~ r2_hidden(C_29,k4_xboole_0(B_28,k1_tarski(C_29))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_13506,plain,(
    ! [C_33539] : ~ r2_hidden(C_33539,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_13477,c_60])).

tff(c_56,plain,(
    ! [A_26] : k3_tarski(k1_tarski(A_26)) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_377,plain,(
    ! [A_117,B_118] :
      ( r2_hidden('#skF_6'(A_117,B_118),A_117)
      | r1_tarski(B_118,k1_setfam_1(A_117))
      | k1_xboole_0 = A_117 ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_38,plain,(
    ! [C_19,A_15] :
      ( C_19 = A_15
      | ~ r2_hidden(C_19,k1_tarski(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_13045,plain,(
    ! [A_32688,B_32689] :
      ( '#skF_6'(k1_tarski(A_32688),B_32689) = A_32688
      | r1_tarski(B_32689,k1_setfam_1(k1_tarski(A_32688)))
      | k1_tarski(A_32688) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_377,c_38])).

tff(c_66,plain,(
    ! [A_31] : r1_tarski(k1_setfam_1(A_31),k3_tarski(A_31)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_180,plain,(
    ! [A_31] :
      ( k3_tarski(A_31) = k1_setfam_1(A_31)
      | ~ r1_tarski(k3_tarski(A_31),k1_setfam_1(A_31)) ) ),
    inference(resolution,[status(thm)],[c_66,c_169])).

tff(c_13085,plain,(
    ! [A_32688] :
      ( k3_tarski(k1_tarski(A_32688)) = k1_setfam_1(k1_tarski(A_32688))
      | '#skF_6'(k1_tarski(A_32688),k3_tarski(k1_tarski(A_32688))) = A_32688
      | k1_tarski(A_32688) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_13045,c_180])).

tff(c_13876,plain,(
    ! [A_34487] :
      ( k1_setfam_1(k1_tarski(A_34487)) = A_34487
      | '#skF_6'(k1_tarski(A_34487),A_34487) = A_34487
      | k1_tarski(A_34487) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_56,c_13085])).

tff(c_13949,plain,
    ( '#skF_6'(k1_tarski('#skF_7'),'#skF_7') = '#skF_7'
    | k1_tarski('#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_13876,c_78])).

tff(c_13959,plain,(
    k1_tarski('#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_13949])).

tff(c_40,plain,(
    ! [C_19] : r2_hidden(C_19,k1_tarski(C_19)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_14038,plain,(
    r2_hidden('#skF_7',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_13959,c_40])).

tff(c_14057,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13506,c_14038])).

tff(c_14059,plain,(
    k1_tarski('#skF_7') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_13949])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_14058,plain,(
    '#skF_6'(k1_tarski('#skF_7'),'#skF_7') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_13949])).

tff(c_74,plain,(
    ! [B_38,A_37] :
      ( ~ r1_tarski(B_38,'#skF_6'(A_37,B_38))
      | r1_tarski(B_38,k1_setfam_1(A_37))
      | k1_xboole_0 = A_37 ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_14069,plain,
    ( ~ r1_tarski('#skF_7','#skF_7')
    | r1_tarski('#skF_7',k1_setfam_1(k1_tarski('#skF_7')))
    | k1_tarski('#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14058,c_74])).

tff(c_14083,plain,
    ( r1_tarski('#skF_7',k1_setfam_1(k1_tarski('#skF_7')))
    | k1_tarski('#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_14069])).

tff(c_14084,plain,(
    r1_tarski('#skF_7',k1_setfam_1(k1_tarski('#skF_7'))) ),
    inference(negUnitSimplification,[status(thm)],[c_14059,c_14083])).

tff(c_396,plain,(
    ! [A_119] :
      ( k3_tarski(A_119) = k1_setfam_1(A_119)
      | ~ r1_tarski(k3_tarski(A_119),k1_setfam_1(A_119)) ) ),
    inference(resolution,[status(thm)],[c_66,c_169])).

tff(c_402,plain,(
    ! [A_26] :
      ( k3_tarski(k1_tarski(A_26)) = k1_setfam_1(k1_tarski(A_26))
      | ~ r1_tarski(A_26,k1_setfam_1(k1_tarski(A_26))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_396])).

tff(c_405,plain,(
    ! [A_26] :
      ( k1_setfam_1(k1_tarski(A_26)) = A_26
      | ~ r1_tarski(A_26,k1_setfam_1(k1_tarski(A_26))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_402])).

tff(c_14137,plain,(
    k1_setfam_1(k1_tarski('#skF_7')) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_14084,c_405])).

tff(c_14149,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_14137])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:47:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.53/3.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.53/3.24  
% 9.53/3.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.53/3.24  %$ r2_hidden > r1_tarski > m1_subset_1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 9.53/3.24  
% 9.53/3.24  %Foreground sorts:
% 9.53/3.24  
% 9.53/3.24  
% 9.53/3.24  %Background operators:
% 9.53/3.24  
% 9.53/3.24  
% 9.53/3.24  %Foreground operators:
% 9.53/3.24  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 9.53/3.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.53/3.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.53/3.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.53/3.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.53/3.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.53/3.24  tff('#skF_7', type, '#skF_7': $i).
% 9.53/3.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.53/3.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.53/3.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.53/3.24  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 9.53/3.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.53/3.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.53/3.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.53/3.24  tff(k3_tarski, type, k3_tarski: $i > $i).
% 9.53/3.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.53/3.24  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 9.53/3.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.53/3.24  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 9.53/3.24  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 9.53/3.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.53/3.24  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 9.53/3.24  
% 9.66/3.26  tff(f_101, negated_conjecture, ~(![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 9.66/3.26  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 9.66/3.26  tff(f_75, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 9.66/3.26  tff(f_77, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 9.66/3.26  tff(f_83, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 9.66/3.26  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.66/3.26  tff(f_68, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 9.66/3.26  tff(f_98, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(B, C))) => ((A = k1_xboole_0) | r1_tarski(B, k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_setfam_1)).
% 9.66/3.26  tff(f_60, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 9.66/3.26  tff(f_79, axiom, (![A]: r1_tarski(k1_setfam_1(A), k3_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_setfam_1)).
% 9.66/3.26  tff(c_78, plain, (k1_setfam_1(k1_tarski('#skF_7'))!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.66/3.26  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.66/3.26  tff(c_215, plain, (![A_78, B_79, C_80]: (r2_hidden(A_78, B_79) | ~r2_hidden(A_78, k4_xboole_0(B_79, k1_tarski(C_80))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.66/3.26  tff(c_13387, plain, (![B_33255, C_33256, B_33257]: (r2_hidden('#skF_1'(k4_xboole_0(B_33255, k1_tarski(C_33256)), B_33257), B_33255) | r1_tarski(k4_xboole_0(B_33255, k1_tarski(C_33256)), B_33257))), inference(resolution, [status(thm)], [c_6, c_215])).
% 9.66/3.26  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.66/3.26  tff(c_13449, plain, (![B_33444, C_33445]: (r1_tarski(k4_xboole_0(B_33444, k1_tarski(C_33445)), B_33444))), inference(resolution, [status(thm)], [c_13387, c_4])).
% 9.66/3.26  tff(c_64, plain, (![A_30]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.66/3.26  tff(c_135, plain, (![A_64, B_65]: (r1_tarski(A_64, B_65) | ~m1_subset_1(A_64, k1_zfmisc_1(B_65)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.66/3.26  tff(c_143, plain, (![A_30]: (r1_tarski(k1_xboole_0, A_30))), inference(resolution, [status(thm)], [c_64, c_135])).
% 9.66/3.26  tff(c_169, plain, (![B_75, A_76]: (B_75=A_76 | ~r1_tarski(B_75, A_76) | ~r1_tarski(A_76, B_75))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.66/3.26  tff(c_178, plain, (![A_30]: (k1_xboole_0=A_30 | ~r1_tarski(A_30, k1_xboole_0))), inference(resolution, [status(thm)], [c_143, c_169])).
% 9.66/3.26  tff(c_13477, plain, (![C_33539]: (k4_xboole_0(k1_xboole_0, k1_tarski(C_33539))=k1_xboole_0)), inference(resolution, [status(thm)], [c_13449, c_178])).
% 9.66/3.26  tff(c_60, plain, (![C_29, B_28]: (~r2_hidden(C_29, k4_xboole_0(B_28, k1_tarski(C_29))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.66/3.26  tff(c_13506, plain, (![C_33539]: (~r2_hidden(C_33539, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_13477, c_60])).
% 9.66/3.26  tff(c_56, plain, (![A_26]: (k3_tarski(k1_tarski(A_26))=A_26)), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.66/3.26  tff(c_377, plain, (![A_117, B_118]: (r2_hidden('#skF_6'(A_117, B_118), A_117) | r1_tarski(B_118, k1_setfam_1(A_117)) | k1_xboole_0=A_117)), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.66/3.26  tff(c_38, plain, (![C_19, A_15]: (C_19=A_15 | ~r2_hidden(C_19, k1_tarski(A_15)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.66/3.26  tff(c_13045, plain, (![A_32688, B_32689]: ('#skF_6'(k1_tarski(A_32688), B_32689)=A_32688 | r1_tarski(B_32689, k1_setfam_1(k1_tarski(A_32688))) | k1_tarski(A_32688)=k1_xboole_0)), inference(resolution, [status(thm)], [c_377, c_38])).
% 9.66/3.26  tff(c_66, plain, (![A_31]: (r1_tarski(k1_setfam_1(A_31), k3_tarski(A_31)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.66/3.26  tff(c_180, plain, (![A_31]: (k3_tarski(A_31)=k1_setfam_1(A_31) | ~r1_tarski(k3_tarski(A_31), k1_setfam_1(A_31)))), inference(resolution, [status(thm)], [c_66, c_169])).
% 9.66/3.26  tff(c_13085, plain, (![A_32688]: (k3_tarski(k1_tarski(A_32688))=k1_setfam_1(k1_tarski(A_32688)) | '#skF_6'(k1_tarski(A_32688), k3_tarski(k1_tarski(A_32688)))=A_32688 | k1_tarski(A_32688)=k1_xboole_0)), inference(resolution, [status(thm)], [c_13045, c_180])).
% 9.66/3.26  tff(c_13876, plain, (![A_34487]: (k1_setfam_1(k1_tarski(A_34487))=A_34487 | '#skF_6'(k1_tarski(A_34487), A_34487)=A_34487 | k1_tarski(A_34487)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_56, c_13085])).
% 9.66/3.26  tff(c_13949, plain, ('#skF_6'(k1_tarski('#skF_7'), '#skF_7')='#skF_7' | k1_tarski('#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_13876, c_78])).
% 9.66/3.26  tff(c_13959, plain, (k1_tarski('#skF_7')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_13949])).
% 9.66/3.26  tff(c_40, plain, (![C_19]: (r2_hidden(C_19, k1_tarski(C_19)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.66/3.26  tff(c_14038, plain, (r2_hidden('#skF_7', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_13959, c_40])).
% 9.66/3.26  tff(c_14057, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13506, c_14038])).
% 9.66/3.26  tff(c_14059, plain, (k1_tarski('#skF_7')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_13949])).
% 9.66/3.26  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.66/3.26  tff(c_14058, plain, ('#skF_6'(k1_tarski('#skF_7'), '#skF_7')='#skF_7'), inference(splitRight, [status(thm)], [c_13949])).
% 9.66/3.26  tff(c_74, plain, (![B_38, A_37]: (~r1_tarski(B_38, '#skF_6'(A_37, B_38)) | r1_tarski(B_38, k1_setfam_1(A_37)) | k1_xboole_0=A_37)), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.66/3.26  tff(c_14069, plain, (~r1_tarski('#skF_7', '#skF_7') | r1_tarski('#skF_7', k1_setfam_1(k1_tarski('#skF_7'))) | k1_tarski('#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_14058, c_74])).
% 9.66/3.26  tff(c_14083, plain, (r1_tarski('#skF_7', k1_setfam_1(k1_tarski('#skF_7'))) | k1_tarski('#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12, c_14069])).
% 9.66/3.26  tff(c_14084, plain, (r1_tarski('#skF_7', k1_setfam_1(k1_tarski('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_14059, c_14083])).
% 9.66/3.26  tff(c_396, plain, (![A_119]: (k3_tarski(A_119)=k1_setfam_1(A_119) | ~r1_tarski(k3_tarski(A_119), k1_setfam_1(A_119)))), inference(resolution, [status(thm)], [c_66, c_169])).
% 9.66/3.26  tff(c_402, plain, (![A_26]: (k3_tarski(k1_tarski(A_26))=k1_setfam_1(k1_tarski(A_26)) | ~r1_tarski(A_26, k1_setfam_1(k1_tarski(A_26))))), inference(superposition, [status(thm), theory('equality')], [c_56, c_396])).
% 9.66/3.26  tff(c_405, plain, (![A_26]: (k1_setfam_1(k1_tarski(A_26))=A_26 | ~r1_tarski(A_26, k1_setfam_1(k1_tarski(A_26))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_402])).
% 9.66/3.26  tff(c_14137, plain, (k1_setfam_1(k1_tarski('#skF_7'))='#skF_7'), inference(resolution, [status(thm)], [c_14084, c_405])).
% 9.66/3.26  tff(c_14149, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_14137])).
% 9.66/3.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.66/3.26  
% 9.66/3.26  Inference rules
% 9.66/3.26  ----------------------
% 9.66/3.26  #Ref     : 0
% 9.66/3.26  #Sup     : 2351
% 9.66/3.26  #Fact    : 38
% 9.66/3.26  #Define  : 0
% 9.66/3.26  #Split   : 7
% 9.66/3.26  #Chain   : 0
% 9.66/3.26  #Close   : 0
% 9.66/3.26  
% 9.66/3.26  Ordering : KBO
% 9.66/3.26  
% 9.66/3.26  Simplification rules
% 9.66/3.26  ----------------------
% 9.66/3.26  #Subsume      : 729
% 9.66/3.26  #Demod        : 714
% 9.66/3.26  #Tautology    : 607
% 9.66/3.26  #SimpNegUnit  : 62
% 9.66/3.26  #BackRed      : 12
% 9.66/3.26  
% 9.66/3.26  #Partial instantiations: 17776
% 9.66/3.26  #Strategies tried      : 1
% 9.66/3.26  
% 9.66/3.26  Timing (in seconds)
% 9.66/3.26  ----------------------
% 9.66/3.26  Preprocessing        : 0.38
% 9.66/3.26  Parsing              : 0.19
% 9.66/3.26  CNF conversion       : 0.03
% 9.66/3.26  Main loop            : 2.03
% 9.66/3.26  Inferencing          : 1.00
% 9.66/3.26  Reduction            : 0.49
% 9.66/3.26  Demodulation         : 0.34
% 9.66/3.26  BG Simplification    : 0.07
% 9.66/3.26  Subsumption          : 0.34
% 9.66/3.26  Abstraction          : 0.10
% 9.66/3.26  MUC search           : 0.00
% 9.66/3.26  Cooper               : 0.00
% 9.66/3.26  Total                : 2.45
% 9.66/3.26  Index Insertion      : 0.00
% 9.66/3.26  Index Deletion       : 0.00
% 9.66/3.26  Index Matching       : 0.00
% 9.66/3.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
