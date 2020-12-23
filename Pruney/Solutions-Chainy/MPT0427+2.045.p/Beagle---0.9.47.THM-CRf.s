%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:02 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 169 expanded)
%              Number of leaves         :   31 (  69 expanded)
%              Depth                    :   12
%              Number of atoms          :  111 ( 317 expanded)
%              Number of equality atoms :   41 (  67 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k1_enumset1 > k8_setfam_1 > k6_setfam_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(c_34,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_42,plain,(
    ! [A_32,B_33] :
      ( r1_tarski(A_32,B_33)
      | ~ m1_subset_1(A_32,k1_zfmisc_1(B_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_50,plain,(
    r1_tarski('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_36,c_42])).

tff(c_119,plain,(
    ! [A_46,C_47,B_48] :
      ( r1_tarski(A_46,C_47)
      | ~ r1_tarski(B_48,C_47)
      | ~ r1_tarski(A_46,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_129,plain,(
    ! [A_46] :
      ( r1_tarski(A_46,k1_zfmisc_1('#skF_2'))
      | ~ r1_tarski(A_46,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_50,c_119])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(k1_tarski(A_10),B_11)
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_138,plain,(
    ! [A_51] :
      ( r1_tarski(A_51,'#skF_4')
      | ~ r1_tarski(A_51,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_34,c_119])).

tff(c_170,plain,(
    ! [A_54] :
      ( r1_tarski(k1_tarski(A_54),'#skF_4')
      | ~ r2_hidden(A_54,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_12,c_138])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( r2_hidden(A_10,B_11)
      | ~ r1_tarski(k1_tarski(A_10),B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_187,plain,(
    ! [A_56] :
      ( r2_hidden(A_56,'#skF_4')
      | ~ r2_hidden(A_56,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_170,c_10])).

tff(c_192,plain,
    ( r2_hidden('#skF_1'('#skF_3'),'#skF_4')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2,c_187])).

tff(c_193,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_192])).

tff(c_28,plain,(
    ! [A_22,B_23] :
      ( m1_subset_1(A_22,k1_zfmisc_1(B_23))
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_182,plain,(
    ! [A_55] :
      ( k8_setfam_1(A_55,k1_xboole_0) = A_55
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_186,plain,(
    ! [A_55] :
      ( k8_setfam_1(A_55,k1_xboole_0) = A_55
      | ~ r1_tarski(k1_xboole_0,k1_zfmisc_1(A_55)) ) ),
    inference(resolution,[status(thm)],[c_28,c_182])).

tff(c_249,plain,(
    ! [A_65] :
      ( k8_setfam_1(A_65,'#skF_3') = A_65
      | ~ r1_tarski('#skF_3',k1_zfmisc_1(A_65)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_193,c_186])).

tff(c_253,plain,
    ( k8_setfam_1('#skF_2','#skF_3') = '#skF_2'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_129,c_249])).

tff(c_263,plain,(
    k8_setfam_1('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_253])).

tff(c_32,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_2','#skF_4'),k8_setfam_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_266,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_32])).

tff(c_451,plain,(
    ! [A_77,B_78] :
      ( m1_subset_1(k8_setfam_1(A_77,B_78),k1_zfmisc_1(A_77))
      | ~ m1_subset_1(B_78,k1_zfmisc_1(k1_zfmisc_1(A_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_26,plain,(
    ! [A_22,B_23] :
      ( r1_tarski(A_22,B_23)
      | ~ m1_subset_1(A_22,k1_zfmisc_1(B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_517,plain,(
    ! [A_84,B_85] :
      ( r1_tarski(k8_setfam_1(A_84,B_85),A_84)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(k1_zfmisc_1(A_84))) ) ),
    inference(resolution,[status(thm)],[c_451,c_26])).

tff(c_527,plain,(
    r1_tarski(k8_setfam_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_517])).

tff(c_535,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_266,c_527])).

tff(c_537,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_192])).

tff(c_30,plain,(
    ! [B_25,A_24] :
      ( r1_tarski(k1_setfam_1(B_25),k1_setfam_1(A_24))
      | k1_xboole_0 = A_24
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_536,plain,(
    r2_hidden('#skF_1'('#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_192])).

tff(c_70,plain,(
    ! [A_40,B_41] :
      ( k2_xboole_0(A_40,B_41) = B_41
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_108,plain,(
    ! [A_44,B_45] :
      ( k2_xboole_0(k1_tarski(A_44),B_45) = B_45
      | ~ r2_hidden(A_44,B_45) ) ),
    inference(resolution,[status(thm)],[c_12,c_70])).

tff(c_16,plain,(
    ! [A_14,B_15] : k2_xboole_0(k1_tarski(A_14),B_15) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_113,plain,(
    ! [B_45,A_44] :
      ( k1_xboole_0 != B_45
      | ~ r2_hidden(A_44,B_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_16])).

tff(c_541,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(resolution,[status(thm)],[c_536,c_113])).

tff(c_589,plain,(
    ! [A_91,B_92] :
      ( k6_setfam_1(A_91,B_92) = k1_setfam_1(B_92)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(k1_zfmisc_1(A_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_602,plain,(
    k6_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_589])).

tff(c_869,plain,(
    ! [A_112,B_113] :
      ( k8_setfam_1(A_112,B_113) = k6_setfam_1(A_112,B_113)
      | k1_xboole_0 = B_113
      | ~ m1_subset_1(B_113,k1_zfmisc_1(k1_zfmisc_1(A_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_883,plain,
    ( k8_setfam_1('#skF_2','#skF_4') = k6_setfam_1('#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_36,c_869])).

tff(c_890,plain,
    ( k8_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_602,c_883])).

tff(c_891,plain,(
    k8_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_541,c_890])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_601,plain,(
    k6_setfam_1('#skF_2','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_589])).

tff(c_880,plain,
    ( k8_setfam_1('#skF_2','#skF_3') = k6_setfam_1('#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_38,c_869])).

tff(c_887,plain,
    ( k8_setfam_1('#skF_2','#skF_3') = k1_setfam_1('#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_601,c_880])).

tff(c_888,plain,(
    k8_setfam_1('#skF_2','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_537,c_887])).

tff(c_895,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_2','#skF_4'),k1_setfam_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_888,c_32])).

tff(c_918,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_4'),k1_setfam_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_891,c_895])).

tff(c_946,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_918])).

tff(c_949,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_946])).

tff(c_951,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_537,c_949])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:28:41 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.67/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.45  
% 2.67/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.45  %$ r2_hidden > r1_tarski > m1_subset_1 > k1_enumset1 > k8_setfam_1 > k6_setfam_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.67/1.45  
% 2.67/1.45  %Foreground sorts:
% 2.67/1.45  
% 2.67/1.45  
% 2.67/1.45  %Background operators:
% 2.67/1.45  
% 2.67/1.45  
% 2.67/1.45  %Foreground operators:
% 2.67/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.67/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.67/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.67/1.45  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.67/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.67/1.45  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 2.67/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.67/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.67/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.67/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.67/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.67/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.67/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.67/1.45  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.67/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.67/1.45  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.67/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.67/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.67/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.67/1.45  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.67/1.45  
% 3.02/1.47  tff(f_93, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_setfam_1)).
% 3.02/1.47  tff(f_77, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.02/1.47  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.02/1.47  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.02/1.47  tff(f_49, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.02/1.47  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_setfam_1)).
% 3.02/1.47  tff(f_69, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 3.02/1.47  tff(f_83, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_setfam_1)).
% 3.02/1.47  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.02/1.47  tff(f_54, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.02/1.47  tff(f_73, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 3.02/1.47  tff(c_34, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.02/1.47  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.02/1.47  tff(c_42, plain, (![A_32, B_33]: (r1_tarski(A_32, B_33) | ~m1_subset_1(A_32, k1_zfmisc_1(B_33)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.02/1.47  tff(c_50, plain, (r1_tarski('#skF_4', k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_36, c_42])).
% 3.02/1.47  tff(c_119, plain, (![A_46, C_47, B_48]: (r1_tarski(A_46, C_47) | ~r1_tarski(B_48, C_47) | ~r1_tarski(A_46, B_48))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.02/1.47  tff(c_129, plain, (![A_46]: (r1_tarski(A_46, k1_zfmisc_1('#skF_2')) | ~r1_tarski(A_46, '#skF_4'))), inference(resolution, [status(thm)], [c_50, c_119])).
% 3.02/1.47  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.02/1.47  tff(c_12, plain, (![A_10, B_11]: (r1_tarski(k1_tarski(A_10), B_11) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.02/1.47  tff(c_138, plain, (![A_51]: (r1_tarski(A_51, '#skF_4') | ~r1_tarski(A_51, '#skF_3'))), inference(resolution, [status(thm)], [c_34, c_119])).
% 3.02/1.47  tff(c_170, plain, (![A_54]: (r1_tarski(k1_tarski(A_54), '#skF_4') | ~r2_hidden(A_54, '#skF_3'))), inference(resolution, [status(thm)], [c_12, c_138])).
% 3.02/1.47  tff(c_10, plain, (![A_10, B_11]: (r2_hidden(A_10, B_11) | ~r1_tarski(k1_tarski(A_10), B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.02/1.47  tff(c_187, plain, (![A_56]: (r2_hidden(A_56, '#skF_4') | ~r2_hidden(A_56, '#skF_3'))), inference(resolution, [status(thm)], [c_170, c_10])).
% 3.02/1.47  tff(c_192, plain, (r2_hidden('#skF_1'('#skF_3'), '#skF_4') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_2, c_187])).
% 3.02/1.47  tff(c_193, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_192])).
% 3.02/1.47  tff(c_28, plain, (![A_22, B_23]: (m1_subset_1(A_22, k1_zfmisc_1(B_23)) | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.02/1.47  tff(c_182, plain, (![A_55]: (k8_setfam_1(A_55, k1_xboole_0)=A_55 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_55))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.02/1.47  tff(c_186, plain, (![A_55]: (k8_setfam_1(A_55, k1_xboole_0)=A_55 | ~r1_tarski(k1_xboole_0, k1_zfmisc_1(A_55)))), inference(resolution, [status(thm)], [c_28, c_182])).
% 3.02/1.47  tff(c_249, plain, (![A_65]: (k8_setfam_1(A_65, '#skF_3')=A_65 | ~r1_tarski('#skF_3', k1_zfmisc_1(A_65)))), inference(demodulation, [status(thm), theory('equality')], [c_193, c_193, c_186])).
% 3.02/1.47  tff(c_253, plain, (k8_setfam_1('#skF_2', '#skF_3')='#skF_2' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_129, c_249])).
% 3.02/1.47  tff(c_263, plain, (k8_setfam_1('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_253])).
% 3.02/1.47  tff(c_32, plain, (~r1_tarski(k8_setfam_1('#skF_2', '#skF_4'), k8_setfam_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.02/1.47  tff(c_266, plain, (~r1_tarski(k8_setfam_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_263, c_32])).
% 3.02/1.47  tff(c_451, plain, (![A_77, B_78]: (m1_subset_1(k8_setfam_1(A_77, B_78), k1_zfmisc_1(A_77)) | ~m1_subset_1(B_78, k1_zfmisc_1(k1_zfmisc_1(A_77))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.02/1.47  tff(c_26, plain, (![A_22, B_23]: (r1_tarski(A_22, B_23) | ~m1_subset_1(A_22, k1_zfmisc_1(B_23)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.02/1.47  tff(c_517, plain, (![A_84, B_85]: (r1_tarski(k8_setfam_1(A_84, B_85), A_84) | ~m1_subset_1(B_85, k1_zfmisc_1(k1_zfmisc_1(A_84))))), inference(resolution, [status(thm)], [c_451, c_26])).
% 3.02/1.47  tff(c_527, plain, (r1_tarski(k8_setfam_1('#skF_2', '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_36, c_517])).
% 3.02/1.47  tff(c_535, plain, $false, inference(negUnitSimplification, [status(thm)], [c_266, c_527])).
% 3.02/1.47  tff(c_537, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_192])).
% 3.02/1.47  tff(c_30, plain, (![B_25, A_24]: (r1_tarski(k1_setfam_1(B_25), k1_setfam_1(A_24)) | k1_xboole_0=A_24 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.02/1.47  tff(c_536, plain, (r2_hidden('#skF_1'('#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_192])).
% 3.02/1.47  tff(c_70, plain, (![A_40, B_41]: (k2_xboole_0(A_40, B_41)=B_41 | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.02/1.47  tff(c_108, plain, (![A_44, B_45]: (k2_xboole_0(k1_tarski(A_44), B_45)=B_45 | ~r2_hidden(A_44, B_45))), inference(resolution, [status(thm)], [c_12, c_70])).
% 3.02/1.47  tff(c_16, plain, (![A_14, B_15]: (k2_xboole_0(k1_tarski(A_14), B_15)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.02/1.47  tff(c_113, plain, (![B_45, A_44]: (k1_xboole_0!=B_45 | ~r2_hidden(A_44, B_45))), inference(superposition, [status(thm), theory('equality')], [c_108, c_16])).
% 3.02/1.47  tff(c_541, plain, (k1_xboole_0!='#skF_4'), inference(resolution, [status(thm)], [c_536, c_113])).
% 3.02/1.47  tff(c_589, plain, (![A_91, B_92]: (k6_setfam_1(A_91, B_92)=k1_setfam_1(B_92) | ~m1_subset_1(B_92, k1_zfmisc_1(k1_zfmisc_1(A_91))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.02/1.47  tff(c_602, plain, (k6_setfam_1('#skF_2', '#skF_4')=k1_setfam_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_589])).
% 3.02/1.47  tff(c_869, plain, (![A_112, B_113]: (k8_setfam_1(A_112, B_113)=k6_setfam_1(A_112, B_113) | k1_xboole_0=B_113 | ~m1_subset_1(B_113, k1_zfmisc_1(k1_zfmisc_1(A_112))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.02/1.47  tff(c_883, plain, (k8_setfam_1('#skF_2', '#skF_4')=k6_setfam_1('#skF_2', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_36, c_869])).
% 3.02/1.47  tff(c_890, plain, (k8_setfam_1('#skF_2', '#skF_4')=k1_setfam_1('#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_602, c_883])).
% 3.02/1.47  tff(c_891, plain, (k8_setfam_1('#skF_2', '#skF_4')=k1_setfam_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_541, c_890])).
% 3.02/1.47  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.02/1.47  tff(c_601, plain, (k6_setfam_1('#skF_2', '#skF_3')=k1_setfam_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_589])).
% 3.02/1.47  tff(c_880, plain, (k8_setfam_1('#skF_2', '#skF_3')=k6_setfam_1('#skF_2', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_38, c_869])).
% 3.02/1.47  tff(c_887, plain, (k8_setfam_1('#skF_2', '#skF_3')=k1_setfam_1('#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_601, c_880])).
% 3.02/1.47  tff(c_888, plain, (k8_setfam_1('#skF_2', '#skF_3')=k1_setfam_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_537, c_887])).
% 3.02/1.47  tff(c_895, plain, (~r1_tarski(k8_setfam_1('#skF_2', '#skF_4'), k1_setfam_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_888, c_32])).
% 3.02/1.47  tff(c_918, plain, (~r1_tarski(k1_setfam_1('#skF_4'), k1_setfam_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_891, c_895])).
% 3.02/1.47  tff(c_946, plain, (k1_xboole_0='#skF_3' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_30, c_918])).
% 3.02/1.47  tff(c_949, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_946])).
% 3.02/1.47  tff(c_951, plain, $false, inference(negUnitSimplification, [status(thm)], [c_537, c_949])).
% 3.02/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/1.47  
% 3.02/1.47  Inference rules
% 3.02/1.47  ----------------------
% 3.02/1.47  #Ref     : 0
% 3.02/1.47  #Sup     : 211
% 3.02/1.47  #Fact    : 0
% 3.02/1.47  #Define  : 0
% 3.02/1.47  #Split   : 6
% 3.02/1.47  #Chain   : 0
% 3.02/1.47  #Close   : 0
% 3.02/1.47  
% 3.02/1.47  Ordering : KBO
% 3.02/1.47  
% 3.02/1.47  Simplification rules
% 3.02/1.47  ----------------------
% 3.02/1.47  #Subsume      : 12
% 3.02/1.47  #Demod        : 46
% 3.02/1.47  #Tautology    : 99
% 3.02/1.47  #SimpNegUnit  : 4
% 3.02/1.47  #BackRed      : 13
% 3.02/1.47  
% 3.02/1.47  #Partial instantiations: 0
% 3.02/1.47  #Strategies tried      : 1
% 3.02/1.47  
% 3.02/1.47  Timing (in seconds)
% 3.02/1.47  ----------------------
% 3.02/1.47  Preprocessing        : 0.33
% 3.02/1.47  Parsing              : 0.18
% 3.02/1.47  CNF conversion       : 0.02
% 3.02/1.47  Main loop            : 0.36
% 3.02/1.47  Inferencing          : 0.14
% 3.02/1.47  Reduction            : 0.10
% 3.02/1.47  Demodulation         : 0.06
% 3.02/1.47  BG Simplification    : 0.02
% 3.02/1.47  Subsumption          : 0.07
% 3.02/1.47  Abstraction          : 0.02
% 3.02/1.47  MUC search           : 0.00
% 3.02/1.47  Cooper               : 0.00
% 3.02/1.47  Total                : 0.72
% 3.02/1.47  Index Insertion      : 0.00
% 3.02/1.47  Index Deletion       : 0.00
% 3.02/1.48  Index Matching       : 0.00
% 3.02/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
