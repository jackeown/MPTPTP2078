%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:25 EST 2020

% Result     : Theorem 5.19s
% Output     : CNFRefutation 5.50s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 118 expanded)
%              Number of leaves         :   39 (  58 expanded)
%              Depth                    :   12
%              Number of atoms          :  105 ( 193 expanded)
%              Number of equality atoms :   23 (  33 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_8 > #skF_3 > #skF_2 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v1_xboole_0(A)
          & v1_zfmisc_1(A) )
       => ! [B] :
            ( ~ v1_xboole_0(k3_xboole_0(A,B))
           => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tex_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_49,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_64,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_96,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_83,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_66,plain,(
    ~ r1_tarski('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_125,plain,(
    ! [D_83,A_84,B_85] :
      ( r2_hidden(D_83,A_84)
      | ~ r2_hidden(D_83,k4_xboole_0(A_84,B_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_130,plain,(
    ! [A_84,B_85] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_84,B_85)),A_84)
      | v1_xboole_0(k4_xboole_0(A_84,B_85)) ) ),
    inference(resolution,[status(thm)],[c_4,c_125])).

tff(c_119,plain,(
    ! [D_80,B_81,A_82] :
      ( ~ r2_hidden(D_80,B_81)
      | ~ r2_hidden(D_80,k4_xboole_0(A_82,B_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_372,plain,(
    ! [A_129,B_130] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(A_129,B_130)),B_130)
      | v1_xboole_0(k4_xboole_0(A_129,B_130)) ) ),
    inference(resolution,[status(thm)],[c_4,c_119])).

tff(c_385,plain,(
    ! [A_84] : v1_xboole_0(k4_xboole_0(A_84,A_84)) ),
    inference(resolution,[status(thm)],[c_130,c_372])).

tff(c_30,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_392,plain,(
    ! [A_132,B_133] :
      ( r2_hidden('#skF_5'(A_132,B_133),B_133)
      | r2_hidden('#skF_6'(A_132,B_133),A_132)
      | B_133 = A_132 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_435,plain,(
    ! [B_134,A_135] :
      ( ~ v1_xboole_0(B_134)
      | r2_hidden('#skF_6'(A_135,B_134),A_135)
      | B_134 = A_135 ) ),
    inference(resolution,[status(thm)],[c_392,c_2])).

tff(c_457,plain,(
    ! [A_136,B_137] :
      ( ~ v1_xboole_0(A_136)
      | ~ v1_xboole_0(B_137)
      | B_137 = A_136 ) ),
    inference(resolution,[status(thm)],[c_435,c_2])).

tff(c_470,plain,(
    ! [B_138] :
      ( ~ v1_xboole_0(B_138)
      | k1_xboole_0 = B_138 ) ),
    inference(resolution,[status(thm)],[c_30,c_457])).

tff(c_491,plain,(
    ! [A_139] : k4_xboole_0(A_139,A_139) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_385,c_470])).

tff(c_46,plain,(
    ! [A_25,B_26] : r1_tarski(k4_xboole_0(A_25,B_26),A_25) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_519,plain,(
    ! [A_139] : r1_tarski(k1_xboole_0,A_139) ),
    inference(superposition,[status(thm),theory(equality)],[c_491,c_46])).

tff(c_483,plain,(
    ! [A_84] : k4_xboole_0(A_84,A_84) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_385,c_470])).

tff(c_32,plain,(
    ! [A_16] : k3_xboole_0(A_16,A_16) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_131,plain,(
    ! [A_86,B_87] : k5_xboole_0(A_86,k3_xboole_0(A_86,B_87)) = k4_xboole_0(A_86,B_87) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_140,plain,(
    ! [A_16] : k5_xboole_0(A_16,A_16) = k4_xboole_0(A_16,A_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_131])).

tff(c_489,plain,(
    ! [A_16] : k5_xboole_0(A_16,A_16) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_483,c_140])).

tff(c_72,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_70,plain,(
    v1_zfmisc_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_44,plain,(
    ! [A_23,B_24] : r1_tarski(k3_xboole_0(A_23,B_24),A_23) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_350,plain,(
    ! [B_124,A_125] :
      ( B_124 = A_125
      | ~ r1_tarski(A_125,B_124)
      | ~ v1_zfmisc_1(B_124)
      | v1_xboole_0(B_124)
      | v1_xboole_0(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_4239,plain,(
    ! [A_377,B_378] :
      ( k3_xboole_0(A_377,B_378) = A_377
      | ~ v1_zfmisc_1(A_377)
      | v1_xboole_0(A_377)
      | v1_xboole_0(k3_xboole_0(A_377,B_378)) ) ),
    inference(resolution,[status(thm)],[c_44,c_350])).

tff(c_68,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_4269,plain,
    ( k3_xboole_0('#skF_7','#skF_8') = '#skF_7'
    | ~ v1_zfmisc_1('#skF_7')
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_4239,c_68])).

tff(c_4309,plain,
    ( k3_xboole_0('#skF_7','#skF_8') = '#skF_7'
    | v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_4269])).

tff(c_4310,plain,(
    k3_xboole_0('#skF_7','#skF_8') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_4309])).

tff(c_42,plain,(
    ! [A_21,B_22] : k5_xboole_0(A_21,k3_xboole_0(A_21,B_22)) = k4_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4364,plain,(
    k5_xboole_0('#skF_7','#skF_7') = k4_xboole_0('#skF_7','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_4310,c_42])).

tff(c_4374,plain,(
    k4_xboole_0('#skF_7','#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_489,c_4364])).

tff(c_258,plain,(
    ! [D_111,A_112,B_113] :
      ( r2_hidden(D_111,k4_xboole_0(A_112,B_113))
      | r2_hidden(D_111,B_113)
      | ~ r2_hidden(D_111,A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_62,plain,(
    ! [B_57,A_56] :
      ( ~ r1_tarski(B_57,A_56)
      | ~ r2_hidden(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_281,plain,(
    ! [A_112,B_113,D_111] :
      ( ~ r1_tarski(k4_xboole_0(A_112,B_113),D_111)
      | r2_hidden(D_111,B_113)
      | ~ r2_hidden(D_111,A_112) ) ),
    inference(resolution,[status(thm)],[c_258,c_62])).

tff(c_4406,plain,(
    ! [D_111] :
      ( ~ r1_tarski(k1_xboole_0,D_111)
      | r2_hidden(D_111,'#skF_8')
      | ~ r2_hidden(D_111,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4374,c_281])).

tff(c_4579,plain,(
    ! [D_380] :
      ( r2_hidden(D_380,'#skF_8')
      | ~ r2_hidden(D_380,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_519,c_4406])).

tff(c_5295,plain,(
    ! [B_408] :
      ( r2_hidden('#skF_2'('#skF_7',B_408),'#skF_8')
      | r1_tarski('#skF_7',B_408) ) ),
    inference(resolution,[status(thm)],[c_10,c_4579])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_5303,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_5295,c_8])).

tff(c_5315,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_66,c_5303])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n012.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 20:11:07 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.19/1.97  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.19/1.98  
% 5.19/1.98  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.19/1.98  %$ r2_hidden > r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_8 > #skF_3 > #skF_2 > #skF_5
% 5.19/1.98  
% 5.19/1.98  %Foreground sorts:
% 5.19/1.98  
% 5.19/1.98  
% 5.19/1.98  %Background operators:
% 5.19/1.98  
% 5.19/1.98  
% 5.19/1.98  %Foreground operators:
% 5.19/1.98  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 5.19/1.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.19/1.98  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.19/1.98  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.19/1.98  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.19/1.98  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.19/1.98  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.19/1.98  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 5.19/1.98  tff('#skF_7', type, '#skF_7': $i).
% 5.19/1.98  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.19/1.98  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.19/1.98  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.19/1.98  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.19/1.98  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.19/1.98  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.19/1.98  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.19/1.98  tff('#skF_8', type, '#skF_8': $i).
% 5.19/1.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.19/1.98  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.19/1.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.19/1.98  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.19/1.98  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 5.19/1.98  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.19/1.98  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.19/1.98  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.19/1.98  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 5.19/1.98  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.19/1.98  
% 5.50/2.00  tff(f_108, negated_conjecture, ~(![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (~v1_xboole_0(k3_xboole_0(A, B)) => r1_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tex_2)).
% 5.50/2.00  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.50/2.00  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.50/2.00  tff(f_48, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 5.50/2.00  tff(f_49, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.50/2.00  tff(f_58, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 5.50/2.00  tff(f_64, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.50/2.00  tff(f_51, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 5.50/2.00  tff(f_60, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.50/2.00  tff(f_62, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 5.50/2.00  tff(f_96, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 5.50/2.00  tff(f_83, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 5.50/2.00  tff(c_66, plain, (~r1_tarski('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.50/2.00  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.50/2.00  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.50/2.00  tff(c_125, plain, (![D_83, A_84, B_85]: (r2_hidden(D_83, A_84) | ~r2_hidden(D_83, k4_xboole_0(A_84, B_85)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.50/2.00  tff(c_130, plain, (![A_84, B_85]: (r2_hidden('#skF_1'(k4_xboole_0(A_84, B_85)), A_84) | v1_xboole_0(k4_xboole_0(A_84, B_85)))), inference(resolution, [status(thm)], [c_4, c_125])).
% 5.50/2.00  tff(c_119, plain, (![D_80, B_81, A_82]: (~r2_hidden(D_80, B_81) | ~r2_hidden(D_80, k4_xboole_0(A_82, B_81)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.50/2.00  tff(c_372, plain, (![A_129, B_130]: (~r2_hidden('#skF_1'(k4_xboole_0(A_129, B_130)), B_130) | v1_xboole_0(k4_xboole_0(A_129, B_130)))), inference(resolution, [status(thm)], [c_4, c_119])).
% 5.50/2.00  tff(c_385, plain, (![A_84]: (v1_xboole_0(k4_xboole_0(A_84, A_84)))), inference(resolution, [status(thm)], [c_130, c_372])).
% 5.50/2.00  tff(c_30, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.50/2.00  tff(c_392, plain, (![A_132, B_133]: (r2_hidden('#skF_5'(A_132, B_133), B_133) | r2_hidden('#skF_6'(A_132, B_133), A_132) | B_133=A_132)), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.50/2.00  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.50/2.00  tff(c_435, plain, (![B_134, A_135]: (~v1_xboole_0(B_134) | r2_hidden('#skF_6'(A_135, B_134), A_135) | B_134=A_135)), inference(resolution, [status(thm)], [c_392, c_2])).
% 5.50/2.00  tff(c_457, plain, (![A_136, B_137]: (~v1_xboole_0(A_136) | ~v1_xboole_0(B_137) | B_137=A_136)), inference(resolution, [status(thm)], [c_435, c_2])).
% 5.50/2.00  tff(c_470, plain, (![B_138]: (~v1_xboole_0(B_138) | k1_xboole_0=B_138)), inference(resolution, [status(thm)], [c_30, c_457])).
% 5.50/2.00  tff(c_491, plain, (![A_139]: (k4_xboole_0(A_139, A_139)=k1_xboole_0)), inference(resolution, [status(thm)], [c_385, c_470])).
% 5.50/2.00  tff(c_46, plain, (![A_25, B_26]: (r1_tarski(k4_xboole_0(A_25, B_26), A_25))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.50/2.00  tff(c_519, plain, (![A_139]: (r1_tarski(k1_xboole_0, A_139))), inference(superposition, [status(thm), theory('equality')], [c_491, c_46])).
% 5.50/2.00  tff(c_483, plain, (![A_84]: (k4_xboole_0(A_84, A_84)=k1_xboole_0)), inference(resolution, [status(thm)], [c_385, c_470])).
% 5.50/2.00  tff(c_32, plain, (![A_16]: (k3_xboole_0(A_16, A_16)=A_16)), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.50/2.00  tff(c_131, plain, (![A_86, B_87]: (k5_xboole_0(A_86, k3_xboole_0(A_86, B_87))=k4_xboole_0(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.50/2.00  tff(c_140, plain, (![A_16]: (k5_xboole_0(A_16, A_16)=k4_xboole_0(A_16, A_16))), inference(superposition, [status(thm), theory('equality')], [c_32, c_131])).
% 5.50/2.00  tff(c_489, plain, (![A_16]: (k5_xboole_0(A_16, A_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_483, c_140])).
% 5.50/2.00  tff(c_72, plain, (~v1_xboole_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.50/2.00  tff(c_70, plain, (v1_zfmisc_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.50/2.00  tff(c_44, plain, (![A_23, B_24]: (r1_tarski(k3_xboole_0(A_23, B_24), A_23))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.50/2.00  tff(c_350, plain, (![B_124, A_125]: (B_124=A_125 | ~r1_tarski(A_125, B_124) | ~v1_zfmisc_1(B_124) | v1_xboole_0(B_124) | v1_xboole_0(A_125))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.50/2.00  tff(c_4239, plain, (![A_377, B_378]: (k3_xboole_0(A_377, B_378)=A_377 | ~v1_zfmisc_1(A_377) | v1_xboole_0(A_377) | v1_xboole_0(k3_xboole_0(A_377, B_378)))), inference(resolution, [status(thm)], [c_44, c_350])).
% 5.50/2.00  tff(c_68, plain, (~v1_xboole_0(k3_xboole_0('#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.50/2.00  tff(c_4269, plain, (k3_xboole_0('#skF_7', '#skF_8')='#skF_7' | ~v1_zfmisc_1('#skF_7') | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_4239, c_68])).
% 5.50/2.00  tff(c_4309, plain, (k3_xboole_0('#skF_7', '#skF_8')='#skF_7' | v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_4269])).
% 5.50/2.00  tff(c_4310, plain, (k3_xboole_0('#skF_7', '#skF_8')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_72, c_4309])).
% 5.50/2.00  tff(c_42, plain, (![A_21, B_22]: (k5_xboole_0(A_21, k3_xboole_0(A_21, B_22))=k4_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.50/2.00  tff(c_4364, plain, (k5_xboole_0('#skF_7', '#skF_7')=k4_xboole_0('#skF_7', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_4310, c_42])).
% 5.50/2.00  tff(c_4374, plain, (k4_xboole_0('#skF_7', '#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_489, c_4364])).
% 5.50/2.00  tff(c_258, plain, (![D_111, A_112, B_113]: (r2_hidden(D_111, k4_xboole_0(A_112, B_113)) | r2_hidden(D_111, B_113) | ~r2_hidden(D_111, A_112))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.50/2.00  tff(c_62, plain, (![B_57, A_56]: (~r1_tarski(B_57, A_56) | ~r2_hidden(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.50/2.00  tff(c_281, plain, (![A_112, B_113, D_111]: (~r1_tarski(k4_xboole_0(A_112, B_113), D_111) | r2_hidden(D_111, B_113) | ~r2_hidden(D_111, A_112))), inference(resolution, [status(thm)], [c_258, c_62])).
% 5.50/2.00  tff(c_4406, plain, (![D_111]: (~r1_tarski(k1_xboole_0, D_111) | r2_hidden(D_111, '#skF_8') | ~r2_hidden(D_111, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_4374, c_281])).
% 5.50/2.00  tff(c_4579, plain, (![D_380]: (r2_hidden(D_380, '#skF_8') | ~r2_hidden(D_380, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_519, c_4406])).
% 5.50/2.00  tff(c_5295, plain, (![B_408]: (r2_hidden('#skF_2'('#skF_7', B_408), '#skF_8') | r1_tarski('#skF_7', B_408))), inference(resolution, [status(thm)], [c_10, c_4579])).
% 5.50/2.00  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.50/2.00  tff(c_5303, plain, (r1_tarski('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_5295, c_8])).
% 5.50/2.00  tff(c_5315, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_66, c_5303])).
% 5.50/2.00  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.50/2.00  
% 5.50/2.00  Inference rules
% 5.50/2.00  ----------------------
% 5.50/2.00  #Ref     : 0
% 5.50/2.00  #Sup     : 1265
% 5.50/2.00  #Fact    : 0
% 5.50/2.00  #Define  : 0
% 5.50/2.00  #Split   : 2
% 5.50/2.00  #Chain   : 0
% 5.50/2.00  #Close   : 0
% 5.50/2.00  
% 5.50/2.00  Ordering : KBO
% 5.50/2.00  
% 5.50/2.00  Simplification rules
% 5.50/2.00  ----------------------
% 5.50/2.00  #Subsume      : 340
% 5.50/2.00  #Demod        : 689
% 5.50/2.00  #Tautology    : 457
% 5.50/2.00  #SimpNegUnit  : 12
% 5.50/2.00  #BackRed      : 52
% 5.50/2.00  
% 5.50/2.00  #Partial instantiations: 0
% 5.50/2.00  #Strategies tried      : 1
% 5.50/2.00  
% 5.50/2.00  Timing (in seconds)
% 5.50/2.00  ----------------------
% 5.50/2.00  Preprocessing        : 0.32
% 5.50/2.00  Parsing              : 0.16
% 5.50/2.00  CNF conversion       : 0.03
% 5.50/2.00  Main loop            : 0.95
% 5.50/2.00  Inferencing          : 0.31
% 5.50/2.00  Reduction            : 0.28
% 5.50/2.00  Demodulation         : 0.20
% 5.50/2.00  BG Simplification    : 0.04
% 5.50/2.00  Subsumption          : 0.25
% 5.50/2.00  Abstraction          : 0.05
% 5.50/2.00  MUC search           : 0.00
% 5.50/2.00  Cooper               : 0.00
% 5.50/2.00  Total                : 1.30
% 5.50/2.00  Index Insertion      : 0.00
% 5.50/2.00  Index Deletion       : 0.00
% 5.50/2.00  Index Matching       : 0.00
% 5.50/2.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
