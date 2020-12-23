%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:39 EST 2020

% Result     : Theorem 3.01s
% Output     : CNFRefutation 3.12s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 133 expanded)
%              Number of leaves         :   29 (  52 expanded)
%              Depth                    :   11
%              Number of atoms          :  121 ( 265 expanded)
%              Number of equality atoms :   26 ( 107 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k7_setfam_1 > k3_subset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_45,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_104,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( ~ ( B != k1_xboole_0
              & k7_setfam_1(A,B) = k1_xboole_0 )
          & ~ ( k7_setfam_1(A,B) != k1_xboole_0
              & B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tops_2)).

tff(f_47,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
         => ( r1_tarski(k7_setfam_1(A,B),k7_setfam_1(A,C))
           => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_setfam_1)).

tff(f_33,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r2_hidden(k3_subset_1(A,C),k7_setfam_1(A,B))
          <=> r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_setfam_1)).

tff(c_14,plain,(
    ! [A_7] : m1_subset_1('#skF_1'(A_7),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_38,plain,
    ( k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_79,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_16,plain,(
    ! [A_9] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_85,plain,(
    ! [A_9] : m1_subset_1('#skF_3',k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_16])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(k7_setfam_1(A_10,B_11),k1_zfmisc_1(k1_zfmisc_1(A_10)))
      | ~ m1_subset_1(B_11,k1_zfmisc_1(k1_zfmisc_1(A_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_125,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(A_44,B_45)
      | ~ m1_subset_1(A_44,k1_zfmisc_1(B_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_133,plain,(
    ! [A_9] : r1_tarski('#skF_3',A_9) ),
    inference(resolution,[status(thm)],[c_85,c_125])).

tff(c_234,plain,(
    ! [A_65,B_66] :
      ( k7_setfam_1(A_65,k7_setfam_1(A_65,B_66)) = B_66
      | ~ m1_subset_1(B_66,k1_zfmisc_1(k1_zfmisc_1(A_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_245,plain,(
    ! [A_65] : k7_setfam_1(A_65,k7_setfam_1(A_65,'#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_85,c_234])).

tff(c_393,plain,(
    ! [B_88,C_89,A_90] :
      ( r1_tarski(B_88,C_89)
      | ~ r1_tarski(k7_setfam_1(A_90,B_88),k7_setfam_1(A_90,C_89))
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k1_zfmisc_1(A_90)))
      | ~ m1_subset_1(B_88,k1_zfmisc_1(k1_zfmisc_1(A_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_402,plain,(
    ! [A_65,C_89] :
      ( r1_tarski(k7_setfam_1(A_65,'#skF_3'),C_89)
      | ~ r1_tarski('#skF_3',k7_setfam_1(A_65,C_89))
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k1_zfmisc_1(A_65)))
      | ~ m1_subset_1(k7_setfam_1(A_65,'#skF_3'),k1_zfmisc_1(k1_zfmisc_1(A_65))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_245,c_393])).

tff(c_657,plain,(
    ! [A_114,C_115] :
      ( r1_tarski(k7_setfam_1(A_114,'#skF_3'),C_115)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k1_zfmisc_1(A_114)))
      | ~ m1_subset_1(k7_setfam_1(A_114,'#skF_3'),k1_zfmisc_1(k1_zfmisc_1(A_114))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_402])).

tff(c_752,plain,(
    ! [A_116] :
      ( r1_tarski(k7_setfam_1(A_116,'#skF_3'),'#skF_3')
      | ~ m1_subset_1(k7_setfam_1(A_116,'#skF_3'),k1_zfmisc_1(k1_zfmisc_1(A_116))) ) ),
    inference(resolution,[status(thm)],[c_85,c_657])).

tff(c_759,plain,(
    ! [A_10] :
      ( r1_tarski(k7_setfam_1(A_10,'#skF_3'),'#skF_3')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(A_10))) ) ),
    inference(resolution,[status(thm)],[c_18,c_752])).

tff(c_770,plain,(
    ! [A_117] : r1_tarski(k7_setfam_1(A_117,'#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_759])).

tff(c_4,plain,(
    ! [A_2] :
      ( k1_xboole_0 = A_2
      | ~ r1_tarski(A_2,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_81,plain,(
    ! [A_2] :
      ( A_2 = '#skF_3'
      | ~ r1_tarski(A_2,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_79,c_4])).

tff(c_779,plain,(
    ! [A_117] : k7_setfam_1(A_117,'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_770,c_81])).

tff(c_44,plain,
    ( k1_xboole_0 != '#skF_3'
    | k7_setfam_1('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_124,plain,(
    k7_setfam_1('#skF_2','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_79,c_44])).

tff(c_802,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_779,c_124])).

tff(c_804,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_22,plain,(
    ! [A_14,B_15] :
      ( r2_hidden(A_14,B_15)
      | v1_xboole_0(B_15)
      | ~ m1_subset_1(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_890,plain,(
    ! [A_129,C_130,B_131] :
      ( m1_subset_1(A_129,C_130)
      | ~ m1_subset_1(B_131,k1_zfmisc_1(C_130))
      | ~ r2_hidden(A_129,B_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_904,plain,(
    ! [A_132] :
      ( m1_subset_1(A_132,k1_zfmisc_1('#skF_2'))
      | ~ r2_hidden(A_132,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_36,c_890])).

tff(c_24,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(A_16,B_17)
      | ~ m1_subset_1(A_16,k1_zfmisc_1(B_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_912,plain,(
    ! [A_133] :
      ( r1_tarski(A_133,'#skF_2')
      | ~ r2_hidden(A_133,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_904,c_24])).

tff(c_917,plain,(
    ! [A_14] :
      ( r1_tarski(A_14,'#skF_2')
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_14,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_912])).

tff(c_931,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_917])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_934,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_931,c_2])).

tff(c_938,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_804,c_934])).

tff(c_940,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_917])).

tff(c_901,plain,(
    ! [A_129] :
      ( m1_subset_1(A_129,k1_zfmisc_1('#skF_2'))
      | ~ r2_hidden(A_129,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_36,c_890])).

tff(c_8,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_71,plain,(
    ! [A_35,B_36] : ~ r2_hidden(A_35,k2_zfmisc_1(A_35,B_36)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_74,plain,(
    ! [A_3] : ~ r2_hidden(A_3,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_71])).

tff(c_803,plain,(
    k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_1119,plain,(
    ! [A_164,C_165,B_166] :
      ( r2_hidden(k3_subset_1(A_164,C_165),k7_setfam_1(A_164,B_166))
      | ~ r2_hidden(C_165,B_166)
      | ~ m1_subset_1(C_165,k1_zfmisc_1(A_164))
      | ~ m1_subset_1(B_166,k1_zfmisc_1(k1_zfmisc_1(A_164))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1135,plain,(
    ! [C_165] :
      ( r2_hidden(k3_subset_1('#skF_2',C_165),k1_xboole_0)
      | ~ r2_hidden(C_165,'#skF_3')
      | ~ m1_subset_1(C_165,k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_803,c_1119])).

tff(c_1143,plain,(
    ! [C_165] :
      ( r2_hidden(k3_subset_1('#skF_2',C_165),k1_xboole_0)
      | ~ r2_hidden(C_165,'#skF_3')
      | ~ m1_subset_1(C_165,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1135])).

tff(c_1145,plain,(
    ! [C_167] :
      ( ~ r2_hidden(C_167,'#skF_3')
      | ~ m1_subset_1(C_167,k1_zfmisc_1('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1143])).

tff(c_1169,plain,(
    ! [A_168] : ~ r2_hidden(A_168,'#skF_3') ),
    inference(resolution,[status(thm)],[c_901,c_1145])).

tff(c_1173,plain,(
    ! [A_14] :
      ( v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_14,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_1169])).

tff(c_1177,plain,(
    ! [A_169] : ~ m1_subset_1(A_169,'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_940,c_1173])).

tff(c_1182,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_14,c_1177])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:30:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.01/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/1.49  
% 3.01/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/1.49  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k7_setfam_1 > k3_subset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 3.01/1.49  
% 3.01/1.49  %Foreground sorts:
% 3.01/1.49  
% 3.01/1.49  
% 3.01/1.49  %Background operators:
% 3.01/1.49  
% 3.01/1.49  
% 3.01/1.49  %Foreground operators:
% 3.01/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.01/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.01/1.49  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.01/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.01/1.49  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 3.01/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.01/1.49  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.01/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.01/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.01/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.01/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.01/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.01/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.01/1.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.01/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.01/1.49  
% 3.12/1.51  tff(f_45, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 3.12/1.51  tff(f_104, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)) & ~(~(k7_setfam_1(A, B) = k1_xboole_0) & (B = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_tops_2)).
% 3.12/1.51  tff(f_47, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.12/1.51  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k7_setfam_1(A, B), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 3.12/1.51  tff(f_65, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.12/1.51  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 3.12/1.51  tff(f_89, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(k7_setfam_1(A, B), k7_setfam_1(A, C)) => r1_tarski(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_setfam_1)).
% 3.12/1.51  tff(f_33, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.12/1.51  tff(f_61, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.12/1.51  tff(f_80, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.12/1.51  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.12/1.51  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.12/1.51  tff(f_42, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 3.12/1.51  tff(f_74, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r2_hidden(k3_subset_1(A, C), k7_setfam_1(A, B)) <=> r2_hidden(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_setfam_1)).
% 3.12/1.51  tff(c_14, plain, (![A_7]: (m1_subset_1('#skF_1'(A_7), A_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.12/1.51  tff(c_38, plain, (k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.12/1.51  tff(c_79, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_38])).
% 3.12/1.51  tff(c_16, plain, (![A_9]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.12/1.51  tff(c_85, plain, (![A_9]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_16])).
% 3.12/1.51  tff(c_18, plain, (![A_10, B_11]: (m1_subset_1(k7_setfam_1(A_10, B_11), k1_zfmisc_1(k1_zfmisc_1(A_10))) | ~m1_subset_1(B_11, k1_zfmisc_1(k1_zfmisc_1(A_10))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.12/1.51  tff(c_125, plain, (![A_44, B_45]: (r1_tarski(A_44, B_45) | ~m1_subset_1(A_44, k1_zfmisc_1(B_45)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.12/1.51  tff(c_133, plain, (![A_9]: (r1_tarski('#skF_3', A_9))), inference(resolution, [status(thm)], [c_85, c_125])).
% 3.12/1.51  tff(c_234, plain, (![A_65, B_66]: (k7_setfam_1(A_65, k7_setfam_1(A_65, B_66))=B_66 | ~m1_subset_1(B_66, k1_zfmisc_1(k1_zfmisc_1(A_65))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.12/1.51  tff(c_245, plain, (![A_65]: (k7_setfam_1(A_65, k7_setfam_1(A_65, '#skF_3'))='#skF_3')), inference(resolution, [status(thm)], [c_85, c_234])).
% 3.12/1.51  tff(c_393, plain, (![B_88, C_89, A_90]: (r1_tarski(B_88, C_89) | ~r1_tarski(k7_setfam_1(A_90, B_88), k7_setfam_1(A_90, C_89)) | ~m1_subset_1(C_89, k1_zfmisc_1(k1_zfmisc_1(A_90))) | ~m1_subset_1(B_88, k1_zfmisc_1(k1_zfmisc_1(A_90))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.12/1.51  tff(c_402, plain, (![A_65, C_89]: (r1_tarski(k7_setfam_1(A_65, '#skF_3'), C_89) | ~r1_tarski('#skF_3', k7_setfam_1(A_65, C_89)) | ~m1_subset_1(C_89, k1_zfmisc_1(k1_zfmisc_1(A_65))) | ~m1_subset_1(k7_setfam_1(A_65, '#skF_3'), k1_zfmisc_1(k1_zfmisc_1(A_65))))), inference(superposition, [status(thm), theory('equality')], [c_245, c_393])).
% 3.12/1.51  tff(c_657, plain, (![A_114, C_115]: (r1_tarski(k7_setfam_1(A_114, '#skF_3'), C_115) | ~m1_subset_1(C_115, k1_zfmisc_1(k1_zfmisc_1(A_114))) | ~m1_subset_1(k7_setfam_1(A_114, '#skF_3'), k1_zfmisc_1(k1_zfmisc_1(A_114))))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_402])).
% 3.12/1.51  tff(c_752, plain, (![A_116]: (r1_tarski(k7_setfam_1(A_116, '#skF_3'), '#skF_3') | ~m1_subset_1(k7_setfam_1(A_116, '#skF_3'), k1_zfmisc_1(k1_zfmisc_1(A_116))))), inference(resolution, [status(thm)], [c_85, c_657])).
% 3.12/1.51  tff(c_759, plain, (![A_10]: (r1_tarski(k7_setfam_1(A_10, '#skF_3'), '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(A_10))))), inference(resolution, [status(thm)], [c_18, c_752])).
% 3.12/1.51  tff(c_770, plain, (![A_117]: (r1_tarski(k7_setfam_1(A_117, '#skF_3'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_759])).
% 3.12/1.51  tff(c_4, plain, (![A_2]: (k1_xboole_0=A_2 | ~r1_tarski(A_2, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.12/1.51  tff(c_81, plain, (![A_2]: (A_2='#skF_3' | ~r1_tarski(A_2, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_79, c_4])).
% 3.12/1.51  tff(c_779, plain, (![A_117]: (k7_setfam_1(A_117, '#skF_3')='#skF_3')), inference(resolution, [status(thm)], [c_770, c_81])).
% 3.12/1.51  tff(c_44, plain, (k1_xboole_0!='#skF_3' | k7_setfam_1('#skF_2', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.12/1.51  tff(c_124, plain, (k7_setfam_1('#skF_2', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_79, c_79, c_44])).
% 3.12/1.51  tff(c_802, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_779, c_124])).
% 3.12/1.51  tff(c_804, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_38])).
% 3.12/1.51  tff(c_22, plain, (![A_14, B_15]: (r2_hidden(A_14, B_15) | v1_xboole_0(B_15) | ~m1_subset_1(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.12/1.51  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.12/1.51  tff(c_890, plain, (![A_129, C_130, B_131]: (m1_subset_1(A_129, C_130) | ~m1_subset_1(B_131, k1_zfmisc_1(C_130)) | ~r2_hidden(A_129, B_131))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.12/1.51  tff(c_904, plain, (![A_132]: (m1_subset_1(A_132, k1_zfmisc_1('#skF_2')) | ~r2_hidden(A_132, '#skF_3'))), inference(resolution, [status(thm)], [c_36, c_890])).
% 3.12/1.51  tff(c_24, plain, (![A_16, B_17]: (r1_tarski(A_16, B_17) | ~m1_subset_1(A_16, k1_zfmisc_1(B_17)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.12/1.51  tff(c_912, plain, (![A_133]: (r1_tarski(A_133, '#skF_2') | ~r2_hidden(A_133, '#skF_3'))), inference(resolution, [status(thm)], [c_904, c_24])).
% 3.12/1.51  tff(c_917, plain, (![A_14]: (r1_tarski(A_14, '#skF_2') | v1_xboole_0('#skF_3') | ~m1_subset_1(A_14, '#skF_3'))), inference(resolution, [status(thm)], [c_22, c_912])).
% 3.12/1.51  tff(c_931, plain, (v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_917])).
% 3.12/1.51  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.12/1.51  tff(c_934, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_931, c_2])).
% 3.12/1.51  tff(c_938, plain, $false, inference(negUnitSimplification, [status(thm)], [c_804, c_934])).
% 3.12/1.51  tff(c_940, plain, (~v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_917])).
% 3.12/1.51  tff(c_901, plain, (![A_129]: (m1_subset_1(A_129, k1_zfmisc_1('#skF_2')) | ~r2_hidden(A_129, '#skF_3'))), inference(resolution, [status(thm)], [c_36, c_890])).
% 3.12/1.51  tff(c_8, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.12/1.51  tff(c_71, plain, (![A_35, B_36]: (~r2_hidden(A_35, k2_zfmisc_1(A_35, B_36)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.12/1.51  tff(c_74, plain, (![A_3]: (~r2_hidden(A_3, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_71])).
% 3.12/1.51  tff(c_803, plain, (k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_38])).
% 3.12/1.51  tff(c_1119, plain, (![A_164, C_165, B_166]: (r2_hidden(k3_subset_1(A_164, C_165), k7_setfam_1(A_164, B_166)) | ~r2_hidden(C_165, B_166) | ~m1_subset_1(C_165, k1_zfmisc_1(A_164)) | ~m1_subset_1(B_166, k1_zfmisc_1(k1_zfmisc_1(A_164))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.12/1.51  tff(c_1135, plain, (![C_165]: (r2_hidden(k3_subset_1('#skF_2', C_165), k1_xboole_0) | ~r2_hidden(C_165, '#skF_3') | ~m1_subset_1(C_165, k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_803, c_1119])).
% 3.12/1.51  tff(c_1143, plain, (![C_165]: (r2_hidden(k3_subset_1('#skF_2', C_165), k1_xboole_0) | ~r2_hidden(C_165, '#skF_3') | ~m1_subset_1(C_165, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1135])).
% 3.12/1.51  tff(c_1145, plain, (![C_167]: (~r2_hidden(C_167, '#skF_3') | ~m1_subset_1(C_167, k1_zfmisc_1('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_74, c_1143])).
% 3.12/1.51  tff(c_1169, plain, (![A_168]: (~r2_hidden(A_168, '#skF_3'))), inference(resolution, [status(thm)], [c_901, c_1145])).
% 3.12/1.51  tff(c_1173, plain, (![A_14]: (v1_xboole_0('#skF_3') | ~m1_subset_1(A_14, '#skF_3'))), inference(resolution, [status(thm)], [c_22, c_1169])).
% 3.12/1.51  tff(c_1177, plain, (![A_169]: (~m1_subset_1(A_169, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_940, c_1173])).
% 3.12/1.51  tff(c_1182, plain, $false, inference(resolution, [status(thm)], [c_14, c_1177])).
% 3.12/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/1.51  
% 3.12/1.51  Inference rules
% 3.12/1.51  ----------------------
% 3.12/1.51  #Ref     : 0
% 3.12/1.51  #Sup     : 258
% 3.12/1.51  #Fact    : 0
% 3.12/1.51  #Define  : 0
% 3.12/1.51  #Split   : 8
% 3.12/1.51  #Chain   : 0
% 3.12/1.51  #Close   : 0
% 3.12/1.51  
% 3.12/1.51  Ordering : KBO
% 3.12/1.51  
% 3.12/1.51  Simplification rules
% 3.12/1.51  ----------------------
% 3.12/1.51  #Subsume      : 38
% 3.12/1.51  #Demod        : 143
% 3.12/1.51  #Tautology    : 117
% 3.12/1.51  #SimpNegUnit  : 10
% 3.12/1.51  #BackRed      : 16
% 3.12/1.51  
% 3.12/1.51  #Partial instantiations: 0
% 3.12/1.51  #Strategies tried      : 1
% 3.12/1.51  
% 3.12/1.51  Timing (in seconds)
% 3.12/1.51  ----------------------
% 3.12/1.51  Preprocessing        : 0.30
% 3.12/1.51  Parsing              : 0.16
% 3.12/1.51  CNF conversion       : 0.02
% 3.12/1.51  Main loop            : 0.40
% 3.12/1.51  Inferencing          : 0.14
% 3.12/1.51  Reduction            : 0.12
% 3.12/1.51  Demodulation         : 0.09
% 3.12/1.51  BG Simplification    : 0.02
% 3.12/1.51  Subsumption          : 0.07
% 3.12/1.51  Abstraction          : 0.02
% 3.12/1.51  MUC search           : 0.00
% 3.12/1.51  Cooper               : 0.00
% 3.12/1.51  Total                : 0.73
% 3.12/1.51  Index Insertion      : 0.00
% 3.12/1.51  Index Deletion       : 0.00
% 3.12/1.51  Index Matching       : 0.00
% 3.12/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
