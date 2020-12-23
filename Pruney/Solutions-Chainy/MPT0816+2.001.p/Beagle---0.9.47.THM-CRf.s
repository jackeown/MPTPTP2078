%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:55 EST 2020

% Result     : Theorem 3.73s
% Output     : CNFRefutation 3.73s
% Verified   : 
% Statistics : Number of formulae       :   58 (  65 expanded)
%              Number of leaves         :   32 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :   71 (  93 expanded)
%              Number of equality atoms :   18 (  18 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k1_enumset1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( ( r1_tarski(k1_relat_1(C),A)
            & r1_tarski(k2_relat_1(C),B) )
         => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k3_xboole_0(B,k2_zfmisc_1(A,k2_relat_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_relat_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(c_10,plain,(
    ! [A_8] : k5_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_38,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_36,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_110,plain,(
    ! [B_41,A_42] :
      ( v4_relat_1(B_41,A_42)
      | ~ r1_tarski(k1_relat_1(B_41),A_42)
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_117,plain,
    ( v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_110])).

tff(c_121,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_117])).

tff(c_28,plain,(
    ! [B_21,A_20] :
      ( k7_relat_1(B_21,A_20) = B_21
      | ~ v4_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_124,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_121,c_28])).

tff(c_127,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_124])).

tff(c_302,plain,(
    ! [B_68,A_69] :
      ( k3_xboole_0(B_68,k2_zfmisc_1(A_69,k2_relat_1(B_68))) = k7_relat_1(B_68,A_69)
      | ~ v1_relat_1(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_6,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_308,plain,(
    ! [B_68,A_69] :
      ( k4_xboole_0(B_68,k2_zfmisc_1(A_69,k2_relat_1(B_68))) = k5_xboole_0(B_68,k7_relat_1(B_68,A_69))
      | ~ v1_relat_1(B_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_302,c_6])).

tff(c_34,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_177,plain,(
    ! [C_51,A_52,B_53] :
      ( r1_tarski(k2_zfmisc_1(C_51,A_52),k2_zfmisc_1(C_51,B_53))
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,C_7)
      | ~ r1_tarski(B_6,C_7)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_692,plain,(
    ! [A_107,C_108,B_109,A_110] :
      ( r1_tarski(A_107,k2_zfmisc_1(C_108,B_109))
      | ~ r1_tarski(A_107,k2_zfmisc_1(C_108,A_110))
      | ~ r1_tarski(A_110,B_109) ) ),
    inference(resolution,[status(thm)],[c_177,c_8])).

tff(c_1276,plain,(
    ! [A_163,C_164,B_165,A_166] :
      ( r1_tarski(A_163,k2_zfmisc_1(C_164,B_165))
      | ~ r1_tarski(A_166,B_165)
      | k4_xboole_0(A_163,k2_zfmisc_1(C_164,A_166)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_692])).

tff(c_1388,plain,(
    ! [A_171,C_172] :
      ( r1_tarski(A_171,k2_zfmisc_1(C_172,'#skF_2'))
      | k4_xboole_0(A_171,k2_zfmisc_1(C_172,k2_relat_1('#skF_3'))) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_34,c_1276])).

tff(c_1400,plain,(
    ! [A_69] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(A_69,'#skF_2'))
      | k5_xboole_0('#skF_3',k7_relat_1('#skF_3',A_69)) != k1_xboole_0
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_1388])).

tff(c_1495,plain,(
    ! [A_177] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(A_177,'#skF_2'))
      | k5_xboole_0('#skF_3',k7_relat_1('#skF_3',A_177)) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1400])).

tff(c_87,plain,(
    ! [A_35,B_36] :
      ( m1_subset_1(A_35,k1_zfmisc_1(B_36))
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_32,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_95,plain,(
    ~ r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_87,c_32])).

tff(c_1514,plain,(
    k5_xboole_0('#skF_3',k7_relat_1('#skF_3','#skF_1')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1495,c_95])).

tff(c_1529,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_127,c_1514])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:26:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.73/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.73/1.56  
% 3.73/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.73/1.56  %$ v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k1_enumset1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.73/1.56  
% 3.73/1.56  %Foreground sorts:
% 3.73/1.56  
% 3.73/1.56  
% 3.73/1.56  %Background operators:
% 3.73/1.56  
% 3.73/1.56  
% 3.73/1.56  %Foreground operators:
% 3.73/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.73/1.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.73/1.56  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.73/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.73/1.56  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.73/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.73/1.56  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.73/1.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.73/1.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.73/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.73/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.73/1.56  tff('#skF_1', type, '#skF_1': $i).
% 3.73/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.73/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.73/1.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.73/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.73/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.73/1.56  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.73/1.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.73/1.56  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.73/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.73/1.56  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.73/1.56  
% 3.73/1.57  tff(f_39, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.73/1.57  tff(f_78, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 3.73/1.57  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.73/1.57  tff(f_65, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.73/1.57  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k3_xboole_0(B, k2_zfmisc_1(A, k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_relat_1)).
% 3.73/1.57  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.73/1.57  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.73/1.57  tff(f_47, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 3.73/1.57  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.73/1.57  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.73/1.57  tff(c_10, plain, (![A_8]: (k5_xboole_0(A_8, A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.73/1.57  tff(c_38, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.73/1.57  tff(c_36, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.73/1.57  tff(c_110, plain, (![B_41, A_42]: (v4_relat_1(B_41, A_42) | ~r1_tarski(k1_relat_1(B_41), A_42) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.73/1.57  tff(c_117, plain, (v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_110])).
% 3.73/1.57  tff(c_121, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_117])).
% 3.73/1.57  tff(c_28, plain, (![B_21, A_20]: (k7_relat_1(B_21, A_20)=B_21 | ~v4_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.73/1.57  tff(c_124, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_121, c_28])).
% 3.73/1.57  tff(c_127, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_124])).
% 3.73/1.57  tff(c_302, plain, (![B_68, A_69]: (k3_xboole_0(B_68, k2_zfmisc_1(A_69, k2_relat_1(B_68)))=k7_relat_1(B_68, A_69) | ~v1_relat_1(B_68))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.73/1.57  tff(c_6, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.73/1.57  tff(c_308, plain, (![B_68, A_69]: (k4_xboole_0(B_68, k2_zfmisc_1(A_69, k2_relat_1(B_68)))=k5_xboole_0(B_68, k7_relat_1(B_68, A_69)) | ~v1_relat_1(B_68))), inference(superposition, [status(thm), theory('equality')], [c_302, c_6])).
% 3.73/1.57  tff(c_34, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.73/1.57  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.73/1.57  tff(c_177, plain, (![C_51, A_52, B_53]: (r1_tarski(k2_zfmisc_1(C_51, A_52), k2_zfmisc_1(C_51, B_53)) | ~r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.73/1.57  tff(c_8, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, C_7) | ~r1_tarski(B_6, C_7) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.73/1.57  tff(c_692, plain, (![A_107, C_108, B_109, A_110]: (r1_tarski(A_107, k2_zfmisc_1(C_108, B_109)) | ~r1_tarski(A_107, k2_zfmisc_1(C_108, A_110)) | ~r1_tarski(A_110, B_109))), inference(resolution, [status(thm)], [c_177, c_8])).
% 3.73/1.57  tff(c_1276, plain, (![A_163, C_164, B_165, A_166]: (r1_tarski(A_163, k2_zfmisc_1(C_164, B_165)) | ~r1_tarski(A_166, B_165) | k4_xboole_0(A_163, k2_zfmisc_1(C_164, A_166))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_692])).
% 3.73/1.57  tff(c_1388, plain, (![A_171, C_172]: (r1_tarski(A_171, k2_zfmisc_1(C_172, '#skF_2')) | k4_xboole_0(A_171, k2_zfmisc_1(C_172, k2_relat_1('#skF_3')))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_1276])).
% 3.73/1.57  tff(c_1400, plain, (![A_69]: (r1_tarski('#skF_3', k2_zfmisc_1(A_69, '#skF_2')) | k5_xboole_0('#skF_3', k7_relat_1('#skF_3', A_69))!=k1_xboole_0 | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_308, c_1388])).
% 3.73/1.57  tff(c_1495, plain, (![A_177]: (r1_tarski('#skF_3', k2_zfmisc_1(A_177, '#skF_2')) | k5_xboole_0('#skF_3', k7_relat_1('#skF_3', A_177))!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1400])).
% 3.73/1.57  tff(c_87, plain, (![A_35, B_36]: (m1_subset_1(A_35, k1_zfmisc_1(B_36)) | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.73/1.57  tff(c_32, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.73/1.57  tff(c_95, plain, (~r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_87, c_32])).
% 3.73/1.57  tff(c_1514, plain, (k5_xboole_0('#skF_3', k7_relat_1('#skF_3', '#skF_1'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_1495, c_95])).
% 3.73/1.57  tff(c_1529, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_127, c_1514])).
% 3.73/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.73/1.57  
% 3.73/1.57  Inference rules
% 3.73/1.57  ----------------------
% 3.73/1.57  #Ref     : 0
% 3.73/1.57  #Sup     : 379
% 3.73/1.57  #Fact    : 0
% 3.73/1.57  #Define  : 0
% 3.73/1.57  #Split   : 2
% 3.73/1.57  #Chain   : 0
% 3.73/1.57  #Close   : 0
% 3.73/1.57  
% 3.73/1.57  Ordering : KBO
% 3.73/1.57  
% 3.73/1.57  Simplification rules
% 3.73/1.57  ----------------------
% 3.73/1.57  #Subsume      : 41
% 3.73/1.57  #Demod        : 32
% 3.73/1.57  #Tautology    : 87
% 3.73/1.57  #SimpNegUnit  : 0
% 3.73/1.57  #BackRed      : 0
% 3.73/1.57  
% 3.73/1.57  #Partial instantiations: 0
% 3.73/1.57  #Strategies tried      : 1
% 3.73/1.57  
% 3.73/1.57  Timing (in seconds)
% 3.73/1.57  ----------------------
% 3.73/1.57  Preprocessing        : 0.29
% 3.73/1.57  Parsing              : 0.16
% 3.73/1.57  CNF conversion       : 0.02
% 3.73/1.57  Main loop            : 0.51
% 3.73/1.58  Inferencing          : 0.17
% 3.73/1.58  Reduction            : 0.13
% 3.73/1.58  Demodulation         : 0.09
% 3.73/1.58  BG Simplification    : 0.02
% 3.73/1.58  Subsumption          : 0.14
% 3.73/1.58  Abstraction          : 0.03
% 3.73/1.58  MUC search           : 0.00
% 3.73/1.58  Cooper               : 0.00
% 3.73/1.58  Total                : 0.83
% 3.73/1.58  Index Insertion      : 0.00
% 3.73/1.58  Index Deletion       : 0.00
% 3.73/1.58  Index Matching       : 0.00
% 3.73/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
