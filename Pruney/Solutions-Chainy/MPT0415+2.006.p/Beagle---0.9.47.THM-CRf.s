%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:46 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :   61 (  82 expanded)
%              Number of leaves         :   34 (  45 expanded)
%              Depth                    :   11
%              Number of atoms          :   73 ( 115 expanded)
%              Number of equality atoms :   14 (  33 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_setfam_1 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_100,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ~ ( B != k1_xboole_0
            & k7_setfam_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_setfam_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_51,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_65,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(f_79,axiom,(
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

tff(c_50,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_162,plain,(
    ! [A_84,C_85,B_86] :
      ( m1_subset_1(A_84,C_85)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(C_85))
      | ~ r2_hidden(A_84,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_167,plain,(
    ! [A_84] :
      ( m1_subset_1(A_84,k1_zfmisc_1('#skF_4'))
      | ~ r2_hidden(A_84,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_52,c_162])).

tff(c_12,plain,(
    ! [A_11] : r1_xboole_0(A_11,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_84,plain,(
    ! [A_68,B_69,C_70] :
      ( ~ r1_xboole_0(A_68,B_69)
      | ~ r2_hidden(C_70,k3_xboole_0(A_68,B_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_90,plain,(
    ! [A_71,B_72] :
      ( ~ r1_xboole_0(A_71,B_72)
      | v1_xboole_0(k3_xboole_0(A_71,B_72)) ) ),
    inference(resolution,[status(thm)],[c_4,c_84])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_95,plain,(
    ! [A_73,B_74] :
      ( k3_xboole_0(A_73,B_74) = k1_xboole_0
      | ~ r1_xboole_0(A_73,B_74) ) ),
    inference(resolution,[status(thm)],[c_90,c_6])).

tff(c_100,plain,(
    ! [A_75] : k3_xboole_0(A_75,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_95])).

tff(c_10,plain,(
    ! [A_6,B_7,C_10] :
      ( ~ r1_xboole_0(A_6,B_7)
      | ~ r2_hidden(C_10,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_108,plain,(
    ! [A_75,C_10] :
      ( ~ r1_xboole_0(A_75,k1_xboole_0)
      | ~ r2_hidden(C_10,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_10])).

tff(c_115,plain,(
    ! [C_10] : ~ r2_hidden(C_10,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_108])).

tff(c_26,plain,(
    ! [A_39] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_39)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_48,plain,(
    k7_setfam_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_181,plain,(
    ! [A_91,B_92] :
      ( k7_setfam_1(A_91,k7_setfam_1(A_91,B_92)) = B_92
      | ~ m1_subset_1(B_92,k1_zfmisc_1(k1_zfmisc_1(A_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_183,plain,(
    k7_setfam_1('#skF_4',k7_setfam_1('#skF_4','#skF_5')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_52,c_181])).

tff(c_188,plain,(
    k7_setfam_1('#skF_4',k1_xboole_0) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_183])).

tff(c_259,plain,(
    ! [A_125,D_126,B_127] :
      ( r2_hidden(k3_subset_1(A_125,D_126),B_127)
      | ~ r2_hidden(D_126,k7_setfam_1(A_125,B_127))
      | ~ m1_subset_1(D_126,k1_zfmisc_1(A_125))
      | ~ m1_subset_1(k7_setfam_1(A_125,B_127),k1_zfmisc_1(k1_zfmisc_1(A_125)))
      | ~ m1_subset_1(B_127,k1_zfmisc_1(k1_zfmisc_1(A_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_263,plain,(
    ! [D_126] :
      ( r2_hidden(k3_subset_1('#skF_4',D_126),k1_xboole_0)
      | ~ r2_hidden(D_126,k7_setfam_1('#skF_4',k1_xboole_0))
      | ~ m1_subset_1(D_126,k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_4')))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_259])).

tff(c_269,plain,(
    ! [D_126] :
      ( r2_hidden(k3_subset_1('#skF_4',D_126),k1_xboole_0)
      | ~ r2_hidden(D_126,'#skF_5')
      | ~ m1_subset_1(D_126,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_52,c_188,c_263])).

tff(c_273,plain,(
    ! [D_128] :
      ( ~ r2_hidden(D_128,'#skF_5')
      | ~ m1_subset_1(D_128,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_269])).

tff(c_289,plain,(
    ! [A_132] : ~ r2_hidden(A_132,'#skF_5') ),
    inference(resolution,[status(thm)],[c_167,c_273])).

tff(c_294,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_289])).

tff(c_297,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_294,c_6])).

tff(c_301,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_297])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:00:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.34/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.31  
% 2.34/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.32  %$ r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_setfam_1 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2
% 2.34/1.32  
% 2.34/1.32  %Foreground sorts:
% 2.34/1.32  
% 2.34/1.32  
% 2.34/1.32  %Background operators:
% 2.34/1.32  
% 2.34/1.32  
% 2.34/1.32  %Foreground operators:
% 2.34/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.34/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.34/1.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.34/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.34/1.32  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 2.34/1.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.34/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.34/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.34/1.32  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.34/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.34/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.34/1.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.34/1.32  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.34/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.34/1.32  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.34/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.34/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.34/1.32  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.34/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.34/1.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.34/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.34/1.32  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.34/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.34/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.34/1.32  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.34/1.32  
% 2.34/1.33  tff(f_100, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_setfam_1)).
% 2.34/1.33  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.34/1.33  tff(f_91, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.34/1.33  tff(f_51, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.34/1.33  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.34/1.33  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.34/1.33  tff(f_65, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.34/1.33  tff(f_83, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 2.34/1.33  tff(f_79, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((C = k7_setfam_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, C) <=> r2_hidden(k3_subset_1(A, D), B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_setfam_1)).
% 2.34/1.33  tff(c_50, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.34/1.33  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.34/1.33  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.34/1.33  tff(c_162, plain, (![A_84, C_85, B_86]: (m1_subset_1(A_84, C_85) | ~m1_subset_1(B_86, k1_zfmisc_1(C_85)) | ~r2_hidden(A_84, B_86))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.34/1.33  tff(c_167, plain, (![A_84]: (m1_subset_1(A_84, k1_zfmisc_1('#skF_4')) | ~r2_hidden(A_84, '#skF_5'))), inference(resolution, [status(thm)], [c_52, c_162])).
% 2.34/1.33  tff(c_12, plain, (![A_11]: (r1_xboole_0(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.34/1.33  tff(c_84, plain, (![A_68, B_69, C_70]: (~r1_xboole_0(A_68, B_69) | ~r2_hidden(C_70, k3_xboole_0(A_68, B_69)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.34/1.33  tff(c_90, plain, (![A_71, B_72]: (~r1_xboole_0(A_71, B_72) | v1_xboole_0(k3_xboole_0(A_71, B_72)))), inference(resolution, [status(thm)], [c_4, c_84])).
% 2.34/1.33  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.34/1.33  tff(c_95, plain, (![A_73, B_74]: (k3_xboole_0(A_73, B_74)=k1_xboole_0 | ~r1_xboole_0(A_73, B_74))), inference(resolution, [status(thm)], [c_90, c_6])).
% 2.34/1.33  tff(c_100, plain, (![A_75]: (k3_xboole_0(A_75, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_95])).
% 2.34/1.33  tff(c_10, plain, (![A_6, B_7, C_10]: (~r1_xboole_0(A_6, B_7) | ~r2_hidden(C_10, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.34/1.33  tff(c_108, plain, (![A_75, C_10]: (~r1_xboole_0(A_75, k1_xboole_0) | ~r2_hidden(C_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_100, c_10])).
% 2.34/1.33  tff(c_115, plain, (![C_10]: (~r2_hidden(C_10, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_108])).
% 2.34/1.33  tff(c_26, plain, (![A_39]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.34/1.33  tff(c_48, plain, (k7_setfam_1('#skF_4', '#skF_5')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.34/1.33  tff(c_181, plain, (![A_91, B_92]: (k7_setfam_1(A_91, k7_setfam_1(A_91, B_92))=B_92 | ~m1_subset_1(B_92, k1_zfmisc_1(k1_zfmisc_1(A_91))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.34/1.33  tff(c_183, plain, (k7_setfam_1('#skF_4', k7_setfam_1('#skF_4', '#skF_5'))='#skF_5'), inference(resolution, [status(thm)], [c_52, c_181])).
% 2.34/1.33  tff(c_188, plain, (k7_setfam_1('#skF_4', k1_xboole_0)='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_183])).
% 2.34/1.33  tff(c_259, plain, (![A_125, D_126, B_127]: (r2_hidden(k3_subset_1(A_125, D_126), B_127) | ~r2_hidden(D_126, k7_setfam_1(A_125, B_127)) | ~m1_subset_1(D_126, k1_zfmisc_1(A_125)) | ~m1_subset_1(k7_setfam_1(A_125, B_127), k1_zfmisc_1(k1_zfmisc_1(A_125))) | ~m1_subset_1(B_127, k1_zfmisc_1(k1_zfmisc_1(A_125))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.34/1.33  tff(c_263, plain, (![D_126]: (r2_hidden(k3_subset_1('#skF_4', D_126), k1_xboole_0) | ~r2_hidden(D_126, k7_setfam_1('#skF_4', k1_xboole_0)) | ~m1_subset_1(D_126, k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_188, c_259])).
% 2.34/1.33  tff(c_269, plain, (![D_126]: (r2_hidden(k3_subset_1('#skF_4', D_126), k1_xboole_0) | ~r2_hidden(D_126, '#skF_5') | ~m1_subset_1(D_126, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_52, c_188, c_263])).
% 2.34/1.33  tff(c_273, plain, (![D_128]: (~r2_hidden(D_128, '#skF_5') | ~m1_subset_1(D_128, k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_115, c_269])).
% 2.34/1.33  tff(c_289, plain, (![A_132]: (~r2_hidden(A_132, '#skF_5'))), inference(resolution, [status(thm)], [c_167, c_273])).
% 2.34/1.33  tff(c_294, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4, c_289])).
% 2.34/1.33  tff(c_297, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_294, c_6])).
% 2.34/1.33  tff(c_301, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_297])).
% 2.34/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.33  
% 2.34/1.33  Inference rules
% 2.34/1.33  ----------------------
% 2.34/1.33  #Ref     : 0
% 2.34/1.33  #Sup     : 55
% 2.34/1.33  #Fact    : 0
% 2.34/1.33  #Define  : 0
% 2.34/1.33  #Split   : 0
% 2.34/1.33  #Chain   : 0
% 2.34/1.33  #Close   : 0
% 2.34/1.33  
% 2.34/1.33  Ordering : KBO
% 2.34/1.33  
% 2.34/1.33  Simplification rules
% 2.34/1.33  ----------------------
% 2.34/1.33  #Subsume      : 8
% 2.34/1.33  #Demod        : 17
% 2.34/1.33  #Tautology    : 33
% 2.34/1.33  #SimpNegUnit  : 3
% 2.34/1.33  #BackRed      : 0
% 2.34/1.33  
% 2.34/1.33  #Partial instantiations: 0
% 2.34/1.33  #Strategies tried      : 1
% 2.34/1.33  
% 2.34/1.33  Timing (in seconds)
% 2.34/1.33  ----------------------
% 2.34/1.33  Preprocessing        : 0.34
% 2.34/1.33  Parsing              : 0.18
% 2.34/1.33  CNF conversion       : 0.02
% 2.34/1.33  Main loop            : 0.20
% 2.34/1.33  Inferencing          : 0.08
% 2.34/1.33  Reduction            : 0.06
% 2.34/1.33  Demodulation         : 0.04
% 2.34/1.33  BG Simplification    : 0.02
% 2.34/1.33  Subsumption          : 0.03
% 2.34/1.33  Abstraction          : 0.01
% 2.34/1.33  MUC search           : 0.00
% 2.34/1.33  Cooper               : 0.00
% 2.34/1.33  Total                : 0.57
% 2.34/1.33  Index Insertion      : 0.00
% 2.34/1.33  Index Deletion       : 0.00
% 2.34/1.33  Index Matching       : 0.00
% 2.34/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
