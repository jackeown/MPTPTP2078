%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:02 EST 2020

% Result     : Theorem 2.90s
% Output     : CNFRefutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 169 expanded)
%              Number of leaves         :   31 (  69 expanded)
%              Depth                    :   12
%              Number of atoms          :  113 ( 317 expanded)
%              Number of equality atoms :   41 (  67 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_93,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(B,C)
             => r1_tarski(k8_setfam_1(A,C),k8_setfam_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(c_34,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_56,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(A_36,B_37)
      | ~ m1_subset_1(A_36,k1_zfmisc_1(B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_68,plain,(
    r1_tarski('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_36,c_56])).

tff(c_119,plain,(
    ! [A_46,C_47,B_48] :
      ( r1_tarski(A_46,C_47)
      | ~ r1_tarski(B_48,C_47)
      | ~ r1_tarski(A_46,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_128,plain,(
    ! [A_46] :
      ( r1_tarski(A_46,k1_zfmisc_1('#skF_2'))
      | ~ r1_tarski(A_46,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_68,c_119])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(k1_tarski(A_12),B_13)
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_138,plain,(
    ! [A_51] :
      ( r1_tarski(A_51,'#skF_4')
      | ~ r1_tarski(A_51,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_34,c_119])).

tff(c_157,plain,(
    ! [A_53] :
      ( r1_tarski(k1_tarski(A_53),'#skF_4')
      | ~ r2_hidden(A_53,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_14,c_138])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( r2_hidden(A_12,B_13)
      | ~ r1_tarski(k1_tarski(A_12),B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_169,plain,(
    ! [A_54] :
      ( r2_hidden(A_54,'#skF_4')
      | ~ r2_hidden(A_54,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_157,c_12])).

tff(c_174,plain,
    ( r2_hidden('#skF_1'('#skF_3'),'#skF_4')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2,c_169])).

tff(c_180,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_174])).

tff(c_28,plain,(
    ! [A_22,B_23] :
      ( m1_subset_1(A_22,k1_zfmisc_1(B_23))
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_175,plain,(
    ! [A_55] :
      ( k8_setfam_1(A_55,k1_xboole_0) = A_55
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_179,plain,(
    ! [A_55] :
      ( k8_setfam_1(A_55,k1_xboole_0) = A_55
      | ~ r1_tarski(k1_xboole_0,k1_zfmisc_1(A_55)) ) ),
    inference(resolution,[status(thm)],[c_28,c_175])).

tff(c_219,plain,(
    ! [A_62] :
      ( k8_setfam_1(A_62,'#skF_3') = A_62
      | ~ r1_tarski('#skF_3',k1_zfmisc_1(A_62)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_180,c_179])).

tff(c_223,plain,
    ( k8_setfam_1('#skF_2','#skF_3') = '#skF_2'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_128,c_219])).

tff(c_233,plain,(
    k8_setfam_1('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_223])).

tff(c_32,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_2','#skF_4'),k8_setfam_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_236,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_32])).

tff(c_456,plain,(
    ! [A_80,B_81] :
      ( m1_subset_1(k8_setfam_1(A_80,B_81),k1_zfmisc_1(A_80))
      | ~ m1_subset_1(B_81,k1_zfmisc_1(k1_zfmisc_1(A_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_26,plain,(
    ! [A_22,B_23] :
      ( r1_tarski(A_22,B_23)
      | ~ m1_subset_1(A_22,k1_zfmisc_1(B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_492,plain,(
    ! [A_84,B_85] :
      ( r1_tarski(k8_setfam_1(A_84,B_85),A_84)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(k1_zfmisc_1(A_84))) ) ),
    inference(resolution,[status(thm)],[c_456,c_26])).

tff(c_502,plain,(
    r1_tarski(k8_setfam_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_492])).

tff(c_510,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_236,c_502])).

tff(c_512,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_174])).

tff(c_30,plain,(
    ! [B_25,A_24] :
      ( r1_tarski(k1_setfam_1(B_25),k1_setfam_1(A_24))
      | k1_xboole_0 = A_24
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_511,plain,(
    r2_hidden('#skF_1'('#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_174])).

tff(c_50,plain,(
    ! [A_32,B_33] :
      ( r1_tarski(k1_tarski(A_32),B_33)
      | ~ r2_hidden(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k2_xboole_0(A_5,B_6) = B_6
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_108,plain,(
    ! [A_44,B_45] :
      ( k2_xboole_0(k1_tarski(A_44),B_45) = B_45
      | ~ r2_hidden(A_44,B_45) ) ),
    inference(resolution,[status(thm)],[c_50,c_6])).

tff(c_16,plain,(
    ! [A_14,B_15] : k2_xboole_0(k1_tarski(A_14),B_15) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_113,plain,(
    ! [B_45,A_44] :
      ( k1_xboole_0 != B_45
      | ~ r2_hidden(A_44,B_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_16])).

tff(c_516,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(resolution,[status(thm)],[c_511,c_113])).

tff(c_562,plain,(
    ! [A_92,B_93] :
      ( k6_setfam_1(A_92,B_93) = k1_setfam_1(B_93)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(k1_zfmisc_1(A_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_575,plain,(
    k6_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_562])).

tff(c_857,plain,(
    ! [A_113,B_114] :
      ( k8_setfam_1(A_113,B_114) = k6_setfam_1(A_113,B_114)
      | k1_xboole_0 = B_114
      | ~ m1_subset_1(B_114,k1_zfmisc_1(k1_zfmisc_1(A_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_871,plain,
    ( k8_setfam_1('#skF_2','#skF_4') = k6_setfam_1('#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_36,c_857])).

tff(c_878,plain,
    ( k8_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_575,c_871])).

tff(c_879,plain,(
    k8_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_516,c_878])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_574,plain,(
    k6_setfam_1('#skF_2','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_562])).

tff(c_868,plain,
    ( k8_setfam_1('#skF_2','#skF_3') = k6_setfam_1('#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_38,c_857])).

tff(c_875,plain,
    ( k8_setfam_1('#skF_2','#skF_3') = k1_setfam_1('#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_574,c_868])).

tff(c_876,plain,(
    k8_setfam_1('#skF_2','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_512,c_875])).

tff(c_883,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_2','#skF_4'),k1_setfam_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_876,c_32])).

tff(c_906,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_4'),k1_setfam_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_879,c_883])).

tff(c_934,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_906])).

tff(c_937,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_934])).

tff(c_939,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_512,c_937])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:36:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.90/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.65  
% 2.90/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.65  %$ r2_hidden > r1_tarski > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.90/1.65  
% 2.90/1.65  %Foreground sorts:
% 2.90/1.65  
% 2.90/1.65  
% 2.90/1.65  %Background operators:
% 2.90/1.65  
% 2.90/1.65  
% 2.90/1.65  %Foreground operators:
% 2.90/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.90/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.90/1.65  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.90/1.65  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.90/1.65  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.90/1.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.90/1.65  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 2.90/1.65  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.90/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.90/1.65  tff('#skF_2', type, '#skF_2': $i).
% 2.90/1.65  tff('#skF_3', type, '#skF_3': $i).
% 2.90/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.90/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.90/1.65  tff('#skF_4', type, '#skF_4': $i).
% 2.90/1.65  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.90/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.90/1.65  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.90/1.65  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.90/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.90/1.65  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.90/1.65  
% 3.24/1.67  tff(f_93, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_setfam_1)).
% 3.24/1.67  tff(f_77, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.24/1.67  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.24/1.67  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.24/1.67  tff(f_51, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.24/1.67  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_setfam_1)).
% 3.24/1.67  tff(f_69, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 3.24/1.67  tff(f_83, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_setfam_1)).
% 3.24/1.67  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.24/1.67  tff(f_54, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.24/1.67  tff(f_73, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 3.24/1.67  tff(c_34, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.24/1.67  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.24/1.67  tff(c_56, plain, (![A_36, B_37]: (r1_tarski(A_36, B_37) | ~m1_subset_1(A_36, k1_zfmisc_1(B_37)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.24/1.67  tff(c_68, plain, (r1_tarski('#skF_4', k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_36, c_56])).
% 3.24/1.67  tff(c_119, plain, (![A_46, C_47, B_48]: (r1_tarski(A_46, C_47) | ~r1_tarski(B_48, C_47) | ~r1_tarski(A_46, B_48))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.24/1.67  tff(c_128, plain, (![A_46]: (r1_tarski(A_46, k1_zfmisc_1('#skF_2')) | ~r1_tarski(A_46, '#skF_4'))), inference(resolution, [status(thm)], [c_68, c_119])).
% 3.24/1.67  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.24/1.67  tff(c_14, plain, (![A_12, B_13]: (r1_tarski(k1_tarski(A_12), B_13) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.24/1.67  tff(c_138, plain, (![A_51]: (r1_tarski(A_51, '#skF_4') | ~r1_tarski(A_51, '#skF_3'))), inference(resolution, [status(thm)], [c_34, c_119])).
% 3.24/1.67  tff(c_157, plain, (![A_53]: (r1_tarski(k1_tarski(A_53), '#skF_4') | ~r2_hidden(A_53, '#skF_3'))), inference(resolution, [status(thm)], [c_14, c_138])).
% 3.24/1.67  tff(c_12, plain, (![A_12, B_13]: (r2_hidden(A_12, B_13) | ~r1_tarski(k1_tarski(A_12), B_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.24/1.67  tff(c_169, plain, (![A_54]: (r2_hidden(A_54, '#skF_4') | ~r2_hidden(A_54, '#skF_3'))), inference(resolution, [status(thm)], [c_157, c_12])).
% 3.24/1.67  tff(c_174, plain, (r2_hidden('#skF_1'('#skF_3'), '#skF_4') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_2, c_169])).
% 3.24/1.67  tff(c_180, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_174])).
% 3.24/1.67  tff(c_28, plain, (![A_22, B_23]: (m1_subset_1(A_22, k1_zfmisc_1(B_23)) | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.24/1.67  tff(c_175, plain, (![A_55]: (k8_setfam_1(A_55, k1_xboole_0)=A_55 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_55))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.24/1.67  tff(c_179, plain, (![A_55]: (k8_setfam_1(A_55, k1_xboole_0)=A_55 | ~r1_tarski(k1_xboole_0, k1_zfmisc_1(A_55)))), inference(resolution, [status(thm)], [c_28, c_175])).
% 3.24/1.67  tff(c_219, plain, (![A_62]: (k8_setfam_1(A_62, '#skF_3')=A_62 | ~r1_tarski('#skF_3', k1_zfmisc_1(A_62)))), inference(demodulation, [status(thm), theory('equality')], [c_180, c_180, c_179])).
% 3.24/1.67  tff(c_223, plain, (k8_setfam_1('#skF_2', '#skF_3')='#skF_2' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_128, c_219])).
% 3.24/1.67  tff(c_233, plain, (k8_setfam_1('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_223])).
% 3.24/1.67  tff(c_32, plain, (~r1_tarski(k8_setfam_1('#skF_2', '#skF_4'), k8_setfam_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.24/1.67  tff(c_236, plain, (~r1_tarski(k8_setfam_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_233, c_32])).
% 3.24/1.67  tff(c_456, plain, (![A_80, B_81]: (m1_subset_1(k8_setfam_1(A_80, B_81), k1_zfmisc_1(A_80)) | ~m1_subset_1(B_81, k1_zfmisc_1(k1_zfmisc_1(A_80))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.24/1.67  tff(c_26, plain, (![A_22, B_23]: (r1_tarski(A_22, B_23) | ~m1_subset_1(A_22, k1_zfmisc_1(B_23)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.24/1.67  tff(c_492, plain, (![A_84, B_85]: (r1_tarski(k8_setfam_1(A_84, B_85), A_84) | ~m1_subset_1(B_85, k1_zfmisc_1(k1_zfmisc_1(A_84))))), inference(resolution, [status(thm)], [c_456, c_26])).
% 3.24/1.67  tff(c_502, plain, (r1_tarski(k8_setfam_1('#skF_2', '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_36, c_492])).
% 3.24/1.67  tff(c_510, plain, $false, inference(negUnitSimplification, [status(thm)], [c_236, c_502])).
% 3.24/1.67  tff(c_512, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_174])).
% 3.24/1.67  tff(c_30, plain, (![B_25, A_24]: (r1_tarski(k1_setfam_1(B_25), k1_setfam_1(A_24)) | k1_xboole_0=A_24 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.24/1.67  tff(c_511, plain, (r2_hidden('#skF_1'('#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_174])).
% 3.24/1.67  tff(c_50, plain, (![A_32, B_33]: (r1_tarski(k1_tarski(A_32), B_33) | ~r2_hidden(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.24/1.67  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, B_6)=B_6 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.24/1.67  tff(c_108, plain, (![A_44, B_45]: (k2_xboole_0(k1_tarski(A_44), B_45)=B_45 | ~r2_hidden(A_44, B_45))), inference(resolution, [status(thm)], [c_50, c_6])).
% 3.24/1.67  tff(c_16, plain, (![A_14, B_15]: (k2_xboole_0(k1_tarski(A_14), B_15)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.24/1.67  tff(c_113, plain, (![B_45, A_44]: (k1_xboole_0!=B_45 | ~r2_hidden(A_44, B_45))), inference(superposition, [status(thm), theory('equality')], [c_108, c_16])).
% 3.24/1.67  tff(c_516, plain, (k1_xboole_0!='#skF_4'), inference(resolution, [status(thm)], [c_511, c_113])).
% 3.24/1.67  tff(c_562, plain, (![A_92, B_93]: (k6_setfam_1(A_92, B_93)=k1_setfam_1(B_93) | ~m1_subset_1(B_93, k1_zfmisc_1(k1_zfmisc_1(A_92))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.24/1.67  tff(c_575, plain, (k6_setfam_1('#skF_2', '#skF_4')=k1_setfam_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_562])).
% 3.24/1.67  tff(c_857, plain, (![A_113, B_114]: (k8_setfam_1(A_113, B_114)=k6_setfam_1(A_113, B_114) | k1_xboole_0=B_114 | ~m1_subset_1(B_114, k1_zfmisc_1(k1_zfmisc_1(A_113))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.24/1.67  tff(c_871, plain, (k8_setfam_1('#skF_2', '#skF_4')=k6_setfam_1('#skF_2', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_36, c_857])).
% 3.24/1.67  tff(c_878, plain, (k8_setfam_1('#skF_2', '#skF_4')=k1_setfam_1('#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_575, c_871])).
% 3.24/1.67  tff(c_879, plain, (k8_setfam_1('#skF_2', '#skF_4')=k1_setfam_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_516, c_878])).
% 3.24/1.67  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.24/1.67  tff(c_574, plain, (k6_setfam_1('#skF_2', '#skF_3')=k1_setfam_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_562])).
% 3.24/1.67  tff(c_868, plain, (k8_setfam_1('#skF_2', '#skF_3')=k6_setfam_1('#skF_2', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_38, c_857])).
% 3.24/1.67  tff(c_875, plain, (k8_setfam_1('#skF_2', '#skF_3')=k1_setfam_1('#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_574, c_868])).
% 3.24/1.67  tff(c_876, plain, (k8_setfam_1('#skF_2', '#skF_3')=k1_setfam_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_512, c_875])).
% 3.24/1.67  tff(c_883, plain, (~r1_tarski(k8_setfam_1('#skF_2', '#skF_4'), k1_setfam_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_876, c_32])).
% 3.24/1.67  tff(c_906, plain, (~r1_tarski(k1_setfam_1('#skF_4'), k1_setfam_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_879, c_883])).
% 3.24/1.67  tff(c_934, plain, (k1_xboole_0='#skF_3' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_30, c_906])).
% 3.24/1.67  tff(c_937, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_934])).
% 3.24/1.67  tff(c_939, plain, $false, inference(negUnitSimplification, [status(thm)], [c_512, c_937])).
% 3.24/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.24/1.67  
% 3.24/1.67  Inference rules
% 3.24/1.67  ----------------------
% 3.24/1.67  #Ref     : 0
% 3.24/1.67  #Sup     : 206
% 3.24/1.67  #Fact    : 0
% 3.24/1.67  #Define  : 0
% 3.24/1.67  #Split   : 6
% 3.24/1.67  #Chain   : 0
% 3.24/1.67  #Close   : 0
% 3.24/1.67  
% 3.24/1.67  Ordering : KBO
% 3.24/1.67  
% 3.24/1.67  Simplification rules
% 3.24/1.67  ----------------------
% 3.24/1.67  #Subsume      : 9
% 3.24/1.67  #Demod        : 43
% 3.24/1.67  #Tautology    : 96
% 3.24/1.67  #SimpNegUnit  : 4
% 3.24/1.67  #BackRed      : 13
% 3.24/1.67  
% 3.24/1.67  #Partial instantiations: 0
% 3.24/1.67  #Strategies tried      : 1
% 3.24/1.67  
% 3.24/1.67  Timing (in seconds)
% 3.24/1.67  ----------------------
% 3.24/1.67  Preprocessing        : 0.40
% 3.24/1.67  Parsing              : 0.21
% 3.24/1.67  CNF conversion       : 0.02
% 3.24/1.67  Main loop            : 0.37
% 3.24/1.67  Inferencing          : 0.14
% 3.24/1.67  Reduction            : 0.11
% 3.24/1.67  Demodulation         : 0.07
% 3.24/1.67  BG Simplification    : 0.02
% 3.24/1.67  Subsumption          : 0.07
% 3.24/1.67  Abstraction          : 0.02
% 3.24/1.67  MUC search           : 0.00
% 3.24/1.67  Cooper               : 0.00
% 3.24/1.67  Total                : 0.81
% 3.24/1.67  Index Insertion      : 0.00
% 3.24/1.67  Index Deletion       : 0.00
% 3.24/1.67  Index Matching       : 0.00
% 3.24/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
