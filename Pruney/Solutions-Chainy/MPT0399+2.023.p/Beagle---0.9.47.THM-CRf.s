%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:34 EST 2020

% Result     : Theorem 3.10s
% Output     : CNFRefutation 3.10s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 152 expanded)
%              Number of leaves         :   24 (  60 expanded)
%              Depth                    :   15
%              Number of atoms          :  120 ( 258 expanded)
%              Number of equality atoms :   19 (  51 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > m1_subset_1 > v1_xboole_0 > #nlpp > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_71,negated_conjecture,(
    ~ ! [A] :
        ( r1_setfam_1(A,k1_xboole_0)
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_setfam_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_39,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_setfam_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

tff(c_28,plain,(
    r1_setfam_1('#skF_4',k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_4,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_8,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_57,plain,(
    ! [A_34,B_35] :
      ( r1_tarski(k3_tarski(A_34),k3_tarski(B_35))
      | ~ r1_setfam_1(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_63,plain,(
    ! [A_34] :
      ( r1_tarski(k3_tarski(A_34),k1_xboole_0)
      | ~ r1_setfam_1(A_34,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_57])).

tff(c_22,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(A_19,k1_zfmisc_1(B_20))
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_329,plain,(
    ! [C_64,B_65,A_66] :
      ( ~ v1_xboole_0(C_64)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(C_64))
      | ~ r2_hidden(A_66,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_333,plain,(
    ! [B_67,A_68,A_69] :
      ( ~ v1_xboole_0(B_67)
      | ~ r2_hidden(A_68,A_69)
      | ~ r1_tarski(A_69,B_67) ) ),
    inference(resolution,[status(thm)],[c_22,c_329])).

tff(c_340,plain,(
    ! [B_70,A_71] :
      ( ~ v1_xboole_0(B_70)
      | ~ r1_tarski(A_71,B_70)
      | k1_xboole_0 = A_71 ) ),
    inference(resolution,[status(thm)],[c_4,c_333])).

tff(c_343,plain,(
    ! [A_34] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | k3_tarski(A_34) = k1_xboole_0
      | ~ r1_setfam_1(A_34,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_63,c_340])).

tff(c_367,plain,(
    ! [A_72] :
      ( k3_tarski(A_72) = k1_xboole_0
      | ~ r1_setfam_1(A_72,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_343])).

tff(c_376,plain,(
    k3_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_367])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,k3_tarski(B_4))
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_399,plain,(
    ! [A_73] :
      ( r1_tarski(A_73,k1_xboole_0)
      | ~ r2_hidden(A_73,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_376,c_6])).

tff(c_407,plain,
    ( r1_tarski('#skF_1'('#skF_4'),k1_xboole_0)
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4,c_399])).

tff(c_411,plain,(
    r1_tarski('#skF_1'('#skF_4'),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_407])).

tff(c_339,plain,(
    ! [B_67,A_1] :
      ( ~ v1_xboole_0(B_67)
      | ~ r1_tarski(A_1,B_67)
      | k1_xboole_0 = A_1 ) ),
    inference(resolution,[status(thm)],[c_4,c_333])).

tff(c_414,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | '#skF_1'('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_411,c_339])).

tff(c_417,plain,(
    '#skF_1'('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_414])).

tff(c_423,plain,
    ( r2_hidden(k1_xboole_0,'#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_417,c_4])).

tff(c_426,plain,(
    r2_hidden(k1_xboole_0,'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_423])).

tff(c_64,plain,(
    ! [B_36] :
      ( r1_tarski(k1_xboole_0,k3_tarski(B_36))
      | ~ r1_setfam_1(k1_xboole_0,B_36) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_57])).

tff(c_67,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ r1_setfam_1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_64])).

tff(c_68,plain,(
    ~ r1_setfam_1(k1_xboole_0,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_67])).

tff(c_51,plain,(
    ! [A_32,B_33] :
      ( r2_hidden('#skF_2'(A_32,B_33),A_32)
      | r1_setfam_1(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_35,plain,(
    ! [A_27,B_28] :
      ( r1_tarski(A_27,k3_tarski(B_28))
      | ~ r2_hidden(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_38,plain,(
    ! [A_27] :
      ( r1_tarski(A_27,k1_xboole_0)
      | ~ r2_hidden(A_27,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_35])).

tff(c_229,plain,(
    ! [B_56] :
      ( r1_tarski('#skF_2'(k1_xboole_0,B_56),k1_xboole_0)
      | r1_setfam_1(k1_xboole_0,B_56) ) ),
    inference(resolution,[status(thm)],[c_51,c_38])).

tff(c_73,plain,(
    ! [C_38,B_39,A_40] :
      ( ~ v1_xboole_0(C_38)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(C_38))
      | ~ r2_hidden(A_40,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_77,plain,(
    ! [B_41,A_42,A_43] :
      ( ~ v1_xboole_0(B_41)
      | ~ r2_hidden(A_42,A_43)
      | ~ r1_tarski(A_43,B_41) ) ),
    inference(resolution,[status(thm)],[c_22,c_73])).

tff(c_83,plain,(
    ! [B_41,A_1] :
      ( ~ v1_xboole_0(B_41)
      | ~ r1_tarski(A_1,B_41)
      | k1_xboole_0 = A_1 ) ),
    inference(resolution,[status(thm)],[c_4,c_77])).

tff(c_235,plain,(
    ! [B_56] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | '#skF_2'(k1_xboole_0,B_56) = k1_xboole_0
      | r1_setfam_1(k1_xboole_0,B_56) ) ),
    inference(resolution,[status(thm)],[c_229,c_83])).

tff(c_264,plain,(
    ! [B_61] :
      ( '#skF_2'(k1_xboole_0,B_61) = k1_xboole_0
      | r1_setfam_1(k1_xboole_0,B_61) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_235])).

tff(c_280,plain,(
    '#skF_2'(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_264,c_68])).

tff(c_16,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_setfam_1(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_301,plain,
    ( r2_hidden(k1_xboole_0,k1_xboole_0)
    | r1_setfam_1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_280,c_16])).

tff(c_307,plain,(
    r2_hidden(k1_xboole_0,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_301])).

tff(c_14,plain,(
    ! [A_5,B_6,D_14] :
      ( ~ r1_tarski('#skF_2'(A_5,B_6),D_14)
      | ~ r2_hidden(D_14,B_6)
      | r1_setfam_1(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_236,plain,(
    ! [B_56] :
      ( ~ r2_hidden(k1_xboole_0,B_56)
      | r1_setfam_1(k1_xboole_0,B_56) ) ),
    inference(resolution,[status(thm)],[c_229,c_14])).

tff(c_311,plain,(
    r1_setfam_1(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_307,c_236])).

tff(c_320,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_311])).

tff(c_321,plain,(
    r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_551,plain,(
    ! [A_87,B_88,C_89] :
      ( r2_hidden('#skF_3'(A_87,B_88,C_89),B_88)
      | ~ r2_hidden(C_89,A_87)
      | ~ r1_setfam_1(A_87,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_332,plain,(
    ! [B_20,A_66,A_19] :
      ( ~ v1_xboole_0(B_20)
      | ~ r2_hidden(A_66,A_19)
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(resolution,[status(thm)],[c_22,c_329])).

tff(c_1400,plain,(
    ! [B_158,B_159,C_160,A_161] :
      ( ~ v1_xboole_0(B_158)
      | ~ r1_tarski(B_159,B_158)
      | ~ r2_hidden(C_160,A_161)
      | ~ r1_setfam_1(A_161,B_159) ) ),
    inference(resolution,[status(thm)],[c_551,c_332])).

tff(c_1412,plain,(
    ! [C_160,A_161] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(C_160,A_161)
      | ~ r1_setfam_1(A_161,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_321,c_1400])).

tff(c_1450,plain,(
    ! [C_164,A_165] :
      ( ~ r2_hidden(C_164,A_165)
      | ~ r1_setfam_1(A_165,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1412])).

tff(c_1456,plain,(
    ~ r1_setfam_1('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_426,c_1450])).

tff(c_1467,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1456])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.36  % Computer   : n007.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 09:40:51 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.10/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.47  
% 3.10/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.47  %$ r2_hidden > r1_tarski > r1_setfam_1 > m1_subset_1 > v1_xboole_0 > #nlpp > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_2
% 3.10/1.47  
% 3.10/1.47  %Foreground sorts:
% 3.10/1.47  
% 3.10/1.47  
% 3.10/1.47  %Background operators:
% 3.10/1.47  
% 3.10/1.47  
% 3.10/1.47  %Foreground operators:
% 3.10/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.10/1.47  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 3.10/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.10/1.47  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.10/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.10/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.10/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.10/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.10/1.47  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.10/1.47  tff('#skF_4', type, '#skF_4': $i).
% 3.10/1.47  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.10/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.10/1.47  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.10/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.10/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.10/1.47  
% 3.10/1.49  tff(f_71, negated_conjecture, ~(![A]: (r1_setfam_1(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_setfam_1)).
% 3.10/1.49  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.10/1.49  tff(f_34, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.10/1.49  tff(f_39, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 3.10/1.49  tff(f_55, axiom, (![A, B]: (r1_setfam_1(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_setfam_1)).
% 3.10/1.49  tff(f_59, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.10/1.49  tff(f_66, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.10/1.49  tff(f_38, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 3.10/1.49  tff(f_51, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_setfam_1)).
% 3.10/1.49  tff(c_28, plain, (r1_setfam_1('#skF_4', k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.10/1.49  tff(c_26, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.10/1.49  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.10/1.49  tff(c_4, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.10/1.49  tff(c_8, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.10/1.49  tff(c_57, plain, (![A_34, B_35]: (r1_tarski(k3_tarski(A_34), k3_tarski(B_35)) | ~r1_setfam_1(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.10/1.49  tff(c_63, plain, (![A_34]: (r1_tarski(k3_tarski(A_34), k1_xboole_0) | ~r1_setfam_1(A_34, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_57])).
% 3.10/1.49  tff(c_22, plain, (![A_19, B_20]: (m1_subset_1(A_19, k1_zfmisc_1(B_20)) | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.10/1.49  tff(c_329, plain, (![C_64, B_65, A_66]: (~v1_xboole_0(C_64) | ~m1_subset_1(B_65, k1_zfmisc_1(C_64)) | ~r2_hidden(A_66, B_65))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.10/1.49  tff(c_333, plain, (![B_67, A_68, A_69]: (~v1_xboole_0(B_67) | ~r2_hidden(A_68, A_69) | ~r1_tarski(A_69, B_67))), inference(resolution, [status(thm)], [c_22, c_329])).
% 3.10/1.49  tff(c_340, plain, (![B_70, A_71]: (~v1_xboole_0(B_70) | ~r1_tarski(A_71, B_70) | k1_xboole_0=A_71)), inference(resolution, [status(thm)], [c_4, c_333])).
% 3.10/1.49  tff(c_343, plain, (![A_34]: (~v1_xboole_0(k1_xboole_0) | k3_tarski(A_34)=k1_xboole_0 | ~r1_setfam_1(A_34, k1_xboole_0))), inference(resolution, [status(thm)], [c_63, c_340])).
% 3.10/1.49  tff(c_367, plain, (![A_72]: (k3_tarski(A_72)=k1_xboole_0 | ~r1_setfam_1(A_72, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_343])).
% 3.10/1.49  tff(c_376, plain, (k3_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_367])).
% 3.10/1.49  tff(c_6, plain, (![A_3, B_4]: (r1_tarski(A_3, k3_tarski(B_4)) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.10/1.49  tff(c_399, plain, (![A_73]: (r1_tarski(A_73, k1_xboole_0) | ~r2_hidden(A_73, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_376, c_6])).
% 3.10/1.49  tff(c_407, plain, (r1_tarski('#skF_1'('#skF_4'), k1_xboole_0) | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_4, c_399])).
% 3.10/1.49  tff(c_411, plain, (r1_tarski('#skF_1'('#skF_4'), k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_26, c_407])).
% 3.10/1.49  tff(c_339, plain, (![B_67, A_1]: (~v1_xboole_0(B_67) | ~r1_tarski(A_1, B_67) | k1_xboole_0=A_1)), inference(resolution, [status(thm)], [c_4, c_333])).
% 3.10/1.49  tff(c_414, plain, (~v1_xboole_0(k1_xboole_0) | '#skF_1'('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_411, c_339])).
% 3.10/1.49  tff(c_417, plain, ('#skF_1'('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_414])).
% 3.10/1.49  tff(c_423, plain, (r2_hidden(k1_xboole_0, '#skF_4') | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_417, c_4])).
% 3.10/1.49  tff(c_426, plain, (r2_hidden(k1_xboole_0, '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_26, c_423])).
% 3.10/1.49  tff(c_64, plain, (![B_36]: (r1_tarski(k1_xboole_0, k3_tarski(B_36)) | ~r1_setfam_1(k1_xboole_0, B_36))), inference(superposition, [status(thm), theory('equality')], [c_8, c_57])).
% 3.10/1.49  tff(c_67, plain, (r1_tarski(k1_xboole_0, k1_xboole_0) | ~r1_setfam_1(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_64])).
% 3.10/1.49  tff(c_68, plain, (~r1_setfam_1(k1_xboole_0, k1_xboole_0)), inference(splitLeft, [status(thm)], [c_67])).
% 3.10/1.49  tff(c_51, plain, (![A_32, B_33]: (r2_hidden('#skF_2'(A_32, B_33), A_32) | r1_setfam_1(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.10/1.49  tff(c_35, plain, (![A_27, B_28]: (r1_tarski(A_27, k3_tarski(B_28)) | ~r2_hidden(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.10/1.49  tff(c_38, plain, (![A_27]: (r1_tarski(A_27, k1_xboole_0) | ~r2_hidden(A_27, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_35])).
% 3.10/1.49  tff(c_229, plain, (![B_56]: (r1_tarski('#skF_2'(k1_xboole_0, B_56), k1_xboole_0) | r1_setfam_1(k1_xboole_0, B_56))), inference(resolution, [status(thm)], [c_51, c_38])).
% 3.10/1.49  tff(c_73, plain, (![C_38, B_39, A_40]: (~v1_xboole_0(C_38) | ~m1_subset_1(B_39, k1_zfmisc_1(C_38)) | ~r2_hidden(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.10/1.49  tff(c_77, plain, (![B_41, A_42, A_43]: (~v1_xboole_0(B_41) | ~r2_hidden(A_42, A_43) | ~r1_tarski(A_43, B_41))), inference(resolution, [status(thm)], [c_22, c_73])).
% 3.10/1.49  tff(c_83, plain, (![B_41, A_1]: (~v1_xboole_0(B_41) | ~r1_tarski(A_1, B_41) | k1_xboole_0=A_1)), inference(resolution, [status(thm)], [c_4, c_77])).
% 3.10/1.49  tff(c_235, plain, (![B_56]: (~v1_xboole_0(k1_xboole_0) | '#skF_2'(k1_xboole_0, B_56)=k1_xboole_0 | r1_setfam_1(k1_xboole_0, B_56))), inference(resolution, [status(thm)], [c_229, c_83])).
% 3.10/1.49  tff(c_264, plain, (![B_61]: ('#skF_2'(k1_xboole_0, B_61)=k1_xboole_0 | r1_setfam_1(k1_xboole_0, B_61))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_235])).
% 3.10/1.49  tff(c_280, plain, ('#skF_2'(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_264, c_68])).
% 3.10/1.49  tff(c_16, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_setfam_1(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.10/1.49  tff(c_301, plain, (r2_hidden(k1_xboole_0, k1_xboole_0) | r1_setfam_1(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_280, c_16])).
% 3.10/1.49  tff(c_307, plain, (r2_hidden(k1_xboole_0, k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_68, c_301])).
% 3.10/1.49  tff(c_14, plain, (![A_5, B_6, D_14]: (~r1_tarski('#skF_2'(A_5, B_6), D_14) | ~r2_hidden(D_14, B_6) | r1_setfam_1(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.10/1.49  tff(c_236, plain, (![B_56]: (~r2_hidden(k1_xboole_0, B_56) | r1_setfam_1(k1_xboole_0, B_56))), inference(resolution, [status(thm)], [c_229, c_14])).
% 3.10/1.49  tff(c_311, plain, (r1_setfam_1(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_307, c_236])).
% 3.10/1.49  tff(c_320, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_311])).
% 3.10/1.49  tff(c_321, plain, (r1_tarski(k1_xboole_0, k1_xboole_0)), inference(splitRight, [status(thm)], [c_67])).
% 3.10/1.49  tff(c_551, plain, (![A_87, B_88, C_89]: (r2_hidden('#skF_3'(A_87, B_88, C_89), B_88) | ~r2_hidden(C_89, A_87) | ~r1_setfam_1(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.10/1.49  tff(c_332, plain, (![B_20, A_66, A_19]: (~v1_xboole_0(B_20) | ~r2_hidden(A_66, A_19) | ~r1_tarski(A_19, B_20))), inference(resolution, [status(thm)], [c_22, c_329])).
% 3.10/1.49  tff(c_1400, plain, (![B_158, B_159, C_160, A_161]: (~v1_xboole_0(B_158) | ~r1_tarski(B_159, B_158) | ~r2_hidden(C_160, A_161) | ~r1_setfam_1(A_161, B_159))), inference(resolution, [status(thm)], [c_551, c_332])).
% 3.10/1.49  tff(c_1412, plain, (![C_160, A_161]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(C_160, A_161) | ~r1_setfam_1(A_161, k1_xboole_0))), inference(resolution, [status(thm)], [c_321, c_1400])).
% 3.10/1.49  tff(c_1450, plain, (![C_164, A_165]: (~r2_hidden(C_164, A_165) | ~r1_setfam_1(A_165, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1412])).
% 3.10/1.49  tff(c_1456, plain, (~r1_setfam_1('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_426, c_1450])).
% 3.10/1.49  tff(c_1467, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_1456])).
% 3.10/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.49  
% 3.10/1.49  Inference rules
% 3.10/1.49  ----------------------
% 3.10/1.49  #Ref     : 0
% 3.10/1.49  #Sup     : 322
% 3.10/1.49  #Fact    : 0
% 3.10/1.49  #Define  : 0
% 3.10/1.49  #Split   : 1
% 3.10/1.49  #Chain   : 0
% 3.10/1.49  #Close   : 0
% 3.10/1.49  
% 3.10/1.49  Ordering : KBO
% 3.10/1.49  
% 3.10/1.49  Simplification rules
% 3.10/1.49  ----------------------
% 3.10/1.49  #Subsume      : 81
% 3.10/1.49  #Demod        : 164
% 3.10/1.49  #Tautology    : 110
% 3.10/1.49  #SimpNegUnit  : 10
% 3.10/1.49  #BackRed      : 3
% 3.10/1.49  
% 3.10/1.49  #Partial instantiations: 0
% 3.10/1.49  #Strategies tried      : 1
% 3.10/1.49  
% 3.10/1.49  Timing (in seconds)
% 3.10/1.49  ----------------------
% 3.10/1.49  Preprocessing        : 0.27
% 3.10/1.49  Parsing              : 0.15
% 3.10/1.49  CNF conversion       : 0.02
% 3.10/1.49  Main loop            : 0.43
% 3.10/1.49  Inferencing          : 0.17
% 3.10/1.49  Reduction            : 0.12
% 3.10/1.49  Demodulation         : 0.08
% 3.10/1.49  BG Simplification    : 0.02
% 3.10/1.49  Subsumption          : 0.09
% 3.10/1.49  Abstraction          : 0.02
% 3.10/1.49  MUC search           : 0.00
% 3.10/1.49  Cooper               : 0.00
% 3.10/1.49  Total                : 0.74
% 3.10/1.49  Index Insertion      : 0.00
% 3.10/1.49  Index Deletion       : 0.00
% 3.10/1.49  Index Matching       : 0.00
% 3.10/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
