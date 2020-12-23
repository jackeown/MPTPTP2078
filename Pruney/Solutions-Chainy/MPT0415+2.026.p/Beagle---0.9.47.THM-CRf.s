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
% DateTime   : Thu Dec  3 09:57:48 EST 2020

% Result     : Theorem 3.50s
% Output     : CNFRefutation 3.50s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 115 expanded)
%              Number of leaves         :   27 (  52 expanded)
%              Depth                    :   13
%              Number of atoms          :   96 ( 218 expanded)
%              Number of equality atoms :   26 (  74 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > m1_subset_1 > k7_setfam_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ~ ( B != k1_xboole_0
            & k7_setfam_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_55,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(f_69,axiom,(
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

tff(f_47,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_95,plain,(
    ! [A_48,C_49,B_50] :
      ( m1_subset_1(A_48,C_49)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(C_49))
      | ~ r2_hidden(A_48,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_100,plain,(
    ! [A_48] :
      ( m1_subset_1(A_48,k1_zfmisc_1('#skF_3'))
      | ~ r2_hidden(A_48,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_42,c_95])).

tff(c_18,plain,(
    ! [A_13] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_38,plain,(
    k7_setfam_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_111,plain,(
    ! [A_53,B_54] :
      ( k7_setfam_1(A_53,k7_setfam_1(A_53,B_54)) = B_54
      | ~ m1_subset_1(B_54,k1_zfmisc_1(k1_zfmisc_1(A_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_113,plain,(
    k7_setfam_1('#skF_3',k7_setfam_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_42,c_111])).

tff(c_118,plain,(
    k7_setfam_1('#skF_3',k1_xboole_0) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_113])).

tff(c_209,plain,(
    ! [A_82,D_83,B_84] :
      ( r2_hidden(k3_subset_1(A_82,D_83),B_84)
      | ~ r2_hidden(D_83,k7_setfam_1(A_82,B_84))
      | ~ m1_subset_1(D_83,k1_zfmisc_1(A_82))
      | ~ m1_subset_1(k7_setfam_1(A_82,B_84),k1_zfmisc_1(k1_zfmisc_1(A_82)))
      | ~ m1_subset_1(B_84,k1_zfmisc_1(k1_zfmisc_1(A_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_213,plain,(
    ! [D_83] :
      ( r2_hidden(k3_subset_1('#skF_3',D_83),k1_xboole_0)
      | ~ r2_hidden(D_83,k7_setfam_1('#skF_3',k1_xboole_0))
      | ~ m1_subset_1(D_83,k1_zfmisc_1('#skF_3'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3')))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_209])).

tff(c_219,plain,(
    ! [D_83] :
      ( r2_hidden(k3_subset_1('#skF_3',D_83),k1_xboole_0)
      | ~ r2_hidden(D_83,'#skF_4')
      | ~ m1_subset_1(D_83,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_42,c_118,c_213])).

tff(c_10,plain,(
    ! [A_8] : k2_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_57,plain,(
    ! [A_32,B_33] : k4_xboole_0(A_32,k2_xboole_0(A_32,B_33)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_64,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_57])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( r1_xboole_0(A_11,B_12)
      | k4_xboole_0(A_11,B_12) != A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_91,plain,(
    ! [A_45,B_46,C_47] :
      ( ~ r1_xboole_0(A_45,B_46)
      | ~ r2_hidden(C_47,B_46)
      | ~ r2_hidden(C_47,A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_164,plain,(
    ! [C_63,B_64,A_65] :
      ( ~ r2_hidden(C_63,B_64)
      | ~ r2_hidden(C_63,A_65)
      | k4_xboole_0(A_65,B_64) != A_65 ) ),
    inference(resolution,[status(thm)],[c_16,c_91])).

tff(c_199,plain,(
    ! [A_79,B_80,A_81] :
      ( ~ r2_hidden('#skF_1'(A_79,B_80),A_81)
      | k4_xboole_0(A_81,B_80) != A_81
      | r1_xboole_0(A_79,B_80) ) ),
    inference(resolution,[status(thm)],[c_4,c_164])).

tff(c_202,plain,(
    ! [B_2,A_1] :
      ( k4_xboole_0(B_2,B_2) != B_2
      | r1_xboole_0(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_199])).

tff(c_225,plain,(
    ! [B_85,A_86] :
      ( k1_xboole_0 != B_85
      | r1_xboole_0(A_86,B_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_202])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = A_11
      | ~ r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_233,plain,(
    ! [A_86] : k4_xboole_0(A_86,k1_xboole_0) = A_86 ),
    inference(resolution,[status(thm)],[c_225,c_14])).

tff(c_450,plain,(
    ! [D_126] :
      ( r2_hidden(k3_subset_1('#skF_3',D_126),k1_xboole_0)
      | ~ r2_hidden(D_126,'#skF_4')
      | ~ m1_subset_1(D_126,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_42,c_118,c_213])).

tff(c_94,plain,(
    ! [C_47,B_12,A_11] :
      ( ~ r2_hidden(C_47,B_12)
      | ~ r2_hidden(C_47,A_11)
      | k4_xboole_0(A_11,B_12) != A_11 ) ),
    inference(resolution,[status(thm)],[c_16,c_91])).

tff(c_463,plain,(
    ! [D_126,A_11] :
      ( ~ r2_hidden(k3_subset_1('#skF_3',D_126),A_11)
      | k4_xboole_0(A_11,k1_xboole_0) != A_11
      | ~ r2_hidden(D_126,'#skF_4')
      | ~ m1_subset_1(D_126,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_450,c_94])).

tff(c_491,plain,(
    ! [D_129,A_130] :
      ( ~ r2_hidden(k3_subset_1('#skF_3',D_129),A_130)
      | ~ r2_hidden(D_129,'#skF_4')
      | ~ m1_subset_1(D_129,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_463])).

tff(c_505,plain,(
    ! [D_131] :
      ( ~ r2_hidden(D_131,'#skF_4')
      | ~ m1_subset_1(D_131,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_219,c_491])).

tff(c_521,plain,(
    ! [A_132] : ~ r2_hidden(A_132,'#skF_4') ),
    inference(resolution,[status(thm)],[c_100,c_505])).

tff(c_543,plain,(
    ! [B_136] : r1_xboole_0('#skF_4',B_136) ),
    inference(resolution,[status(thm)],[c_6,c_521])).

tff(c_570,plain,(
    ! [B_139] : k4_xboole_0('#skF_4',B_139) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_543,c_14])).

tff(c_583,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_570,c_64])).

tff(c_607,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_583])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:22:17 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.50/1.82  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.50/1.82  
% 3.50/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.50/1.83  %$ r2_hidden > r1_xboole_0 > m1_subset_1 > k7_setfam_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 3.50/1.83  
% 3.50/1.83  %Foreground sorts:
% 3.50/1.83  
% 3.50/1.83  
% 3.50/1.83  %Background operators:
% 3.50/1.83  
% 3.50/1.83  
% 3.50/1.83  %Foreground operators:
% 3.50/1.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.50/1.83  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.50/1.83  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.50/1.83  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.50/1.83  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 3.50/1.83  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.50/1.83  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.50/1.83  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.50/1.83  tff('#skF_3', type, '#skF_3': $i).
% 3.50/1.83  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.50/1.83  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.50/1.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.50/1.83  tff('#skF_4', type, '#skF_4': $i).
% 3.50/1.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.50/1.83  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.50/1.83  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.50/1.83  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.50/1.83  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.50/1.83  
% 3.50/1.85  tff(f_88, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_setfam_1)).
% 3.50/1.85  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.50/1.85  tff(f_79, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 3.50/1.85  tff(f_55, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.50/1.85  tff(f_73, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 3.50/1.85  tff(f_69, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((C = k7_setfam_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, C) <=> r2_hidden(k3_subset_1(A, D), B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_setfam_1)).
% 3.50/1.85  tff(f_47, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.50/1.85  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.50/1.85  tff(f_53, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.50/1.85  tff(c_40, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.50/1.85  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.50/1.85  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.50/1.85  tff(c_95, plain, (![A_48, C_49, B_50]: (m1_subset_1(A_48, C_49) | ~m1_subset_1(B_50, k1_zfmisc_1(C_49)) | ~r2_hidden(A_48, B_50))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.50/1.85  tff(c_100, plain, (![A_48]: (m1_subset_1(A_48, k1_zfmisc_1('#skF_3')) | ~r2_hidden(A_48, '#skF_4'))), inference(resolution, [status(thm)], [c_42, c_95])).
% 3.50/1.85  tff(c_18, plain, (![A_13]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.50/1.85  tff(c_38, plain, (k7_setfam_1('#skF_3', '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.50/1.85  tff(c_111, plain, (![A_53, B_54]: (k7_setfam_1(A_53, k7_setfam_1(A_53, B_54))=B_54 | ~m1_subset_1(B_54, k1_zfmisc_1(k1_zfmisc_1(A_53))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.50/1.85  tff(c_113, plain, (k7_setfam_1('#skF_3', k7_setfam_1('#skF_3', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_42, c_111])).
% 3.50/1.85  tff(c_118, plain, (k7_setfam_1('#skF_3', k1_xboole_0)='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_113])).
% 3.50/1.85  tff(c_209, plain, (![A_82, D_83, B_84]: (r2_hidden(k3_subset_1(A_82, D_83), B_84) | ~r2_hidden(D_83, k7_setfam_1(A_82, B_84)) | ~m1_subset_1(D_83, k1_zfmisc_1(A_82)) | ~m1_subset_1(k7_setfam_1(A_82, B_84), k1_zfmisc_1(k1_zfmisc_1(A_82))) | ~m1_subset_1(B_84, k1_zfmisc_1(k1_zfmisc_1(A_82))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.50/1.85  tff(c_213, plain, (![D_83]: (r2_hidden(k3_subset_1('#skF_3', D_83), k1_xboole_0) | ~r2_hidden(D_83, k7_setfam_1('#skF_3', k1_xboole_0)) | ~m1_subset_1(D_83, k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_118, c_209])).
% 3.50/1.85  tff(c_219, plain, (![D_83]: (r2_hidden(k3_subset_1('#skF_3', D_83), k1_xboole_0) | ~r2_hidden(D_83, '#skF_4') | ~m1_subset_1(D_83, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_42, c_118, c_213])).
% 3.50/1.85  tff(c_10, plain, (![A_8]: (k2_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.50/1.85  tff(c_57, plain, (![A_32, B_33]: (k4_xboole_0(A_32, k2_xboole_0(A_32, B_33))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.50/1.85  tff(c_64, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_57])).
% 3.50/1.85  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.50/1.85  tff(c_16, plain, (![A_11, B_12]: (r1_xboole_0(A_11, B_12) | k4_xboole_0(A_11, B_12)!=A_11)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.50/1.85  tff(c_91, plain, (![A_45, B_46, C_47]: (~r1_xboole_0(A_45, B_46) | ~r2_hidden(C_47, B_46) | ~r2_hidden(C_47, A_45))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.50/1.85  tff(c_164, plain, (![C_63, B_64, A_65]: (~r2_hidden(C_63, B_64) | ~r2_hidden(C_63, A_65) | k4_xboole_0(A_65, B_64)!=A_65)), inference(resolution, [status(thm)], [c_16, c_91])).
% 3.50/1.85  tff(c_199, plain, (![A_79, B_80, A_81]: (~r2_hidden('#skF_1'(A_79, B_80), A_81) | k4_xboole_0(A_81, B_80)!=A_81 | r1_xboole_0(A_79, B_80))), inference(resolution, [status(thm)], [c_4, c_164])).
% 3.50/1.85  tff(c_202, plain, (![B_2, A_1]: (k4_xboole_0(B_2, B_2)!=B_2 | r1_xboole_0(A_1, B_2))), inference(resolution, [status(thm)], [c_4, c_199])).
% 3.50/1.85  tff(c_225, plain, (![B_85, A_86]: (k1_xboole_0!=B_85 | r1_xboole_0(A_86, B_85))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_202])).
% 3.50/1.85  tff(c_14, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)=A_11 | ~r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.50/1.85  tff(c_233, plain, (![A_86]: (k4_xboole_0(A_86, k1_xboole_0)=A_86)), inference(resolution, [status(thm)], [c_225, c_14])).
% 3.50/1.85  tff(c_450, plain, (![D_126]: (r2_hidden(k3_subset_1('#skF_3', D_126), k1_xboole_0) | ~r2_hidden(D_126, '#skF_4') | ~m1_subset_1(D_126, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_42, c_118, c_213])).
% 3.50/1.85  tff(c_94, plain, (![C_47, B_12, A_11]: (~r2_hidden(C_47, B_12) | ~r2_hidden(C_47, A_11) | k4_xboole_0(A_11, B_12)!=A_11)), inference(resolution, [status(thm)], [c_16, c_91])).
% 3.50/1.85  tff(c_463, plain, (![D_126, A_11]: (~r2_hidden(k3_subset_1('#skF_3', D_126), A_11) | k4_xboole_0(A_11, k1_xboole_0)!=A_11 | ~r2_hidden(D_126, '#skF_4') | ~m1_subset_1(D_126, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_450, c_94])).
% 3.50/1.85  tff(c_491, plain, (![D_129, A_130]: (~r2_hidden(k3_subset_1('#skF_3', D_129), A_130) | ~r2_hidden(D_129, '#skF_4') | ~m1_subset_1(D_129, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_233, c_463])).
% 3.50/1.85  tff(c_505, plain, (![D_131]: (~r2_hidden(D_131, '#skF_4') | ~m1_subset_1(D_131, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_219, c_491])).
% 3.50/1.85  tff(c_521, plain, (![A_132]: (~r2_hidden(A_132, '#skF_4'))), inference(resolution, [status(thm)], [c_100, c_505])).
% 3.50/1.85  tff(c_543, plain, (![B_136]: (r1_xboole_0('#skF_4', B_136))), inference(resolution, [status(thm)], [c_6, c_521])).
% 3.50/1.85  tff(c_570, plain, (![B_139]: (k4_xboole_0('#skF_4', B_139)='#skF_4')), inference(resolution, [status(thm)], [c_543, c_14])).
% 3.50/1.85  tff(c_583, plain, (k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_570, c_64])).
% 3.50/1.85  tff(c_607, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_583])).
% 3.50/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.50/1.85  
% 3.50/1.85  Inference rules
% 3.50/1.85  ----------------------
% 3.50/1.85  #Ref     : 0
% 3.50/1.85  #Sup     : 138
% 3.50/1.85  #Fact    : 0
% 3.50/1.85  #Define  : 0
% 3.50/1.85  #Split   : 0
% 3.50/1.85  #Chain   : 0
% 3.50/1.85  #Close   : 0
% 3.50/1.85  
% 3.50/1.85  Ordering : KBO
% 3.50/1.85  
% 3.50/1.85  Simplification rules
% 3.50/1.85  ----------------------
% 3.50/1.85  #Subsume      : 28
% 3.50/1.85  #Demod        : 28
% 3.50/1.85  #Tautology    : 41
% 3.50/1.85  #SimpNegUnit  : 2
% 3.50/1.85  #BackRed      : 1
% 3.50/1.85  
% 3.50/1.85  #Partial instantiations: 0
% 3.50/1.85  #Strategies tried      : 1
% 3.50/1.85  
% 3.50/1.85  Timing (in seconds)
% 3.50/1.85  ----------------------
% 3.50/1.86  Preprocessing        : 0.50
% 3.50/1.86  Parsing              : 0.25
% 3.50/1.86  CNF conversion       : 0.04
% 3.50/1.86  Main loop            : 0.52
% 3.50/1.86  Inferencing          : 0.20
% 3.50/1.86  Reduction            : 0.14
% 3.50/1.86  Demodulation         : 0.10
% 3.50/1.86  BG Simplification    : 0.03
% 3.50/1.86  Subsumption          : 0.11
% 3.50/1.86  Abstraction          : 0.03
% 3.50/1.86  MUC search           : 0.00
% 3.50/1.86  Cooper               : 0.00
% 3.50/1.86  Total                : 1.06
% 3.50/1.86  Index Insertion      : 0.00
% 3.50/1.86  Index Deletion       : 0.00
% 3.50/1.86  Index Matching       : 0.00
% 3.50/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
