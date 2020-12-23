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
% DateTime   : Thu Dec  3 09:55:50 EST 2020

% Result     : Theorem 10.91s
% Output     : CNFRefutation 11.11s
% Verified   : 
% Statistics : Number of formulae       :   72 (  96 expanded)
%              Number of leaves         :   30 (  44 expanded)
%              Depth                    :    9
%              Number of atoms          :   96 ( 157 expanded)
%              Number of equality atoms :   12 (  19 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(B,C)
            <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_88,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(C,B),k4_xboole_0(C,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).

tff(c_52,plain,
    ( ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4'))
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_110,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_46,plain,(
    ! [A_34] : ~ v1_xboole_0(k1_zfmisc_1(A_34)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_241,plain,(
    ! [B_67,A_68] :
      ( r2_hidden(B_67,A_68)
      | ~ m1_subset_1(B_67,A_68)
      | v1_xboole_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_24,plain,(
    ! [C_29,A_25] :
      ( r1_tarski(C_29,A_25)
      | ~ r2_hidden(C_29,k1_zfmisc_1(A_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_245,plain,(
    ! [B_67,A_25] :
      ( r1_tarski(B_67,A_25)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(A_25))
      | v1_xboole_0(k1_zfmisc_1(A_25)) ) ),
    inference(resolution,[status(thm)],[c_241,c_24])).

tff(c_249,plain,(
    ! [B_69,A_70] :
      ( r1_tarski(B_69,A_70)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_70)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_245])).

tff(c_262,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_249])).

tff(c_58,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_191,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_58])).

tff(c_595,plain,(
    ! [A_117,B_118] :
      ( k4_xboole_0(A_117,B_118) = k3_subset_1(A_117,B_118)
      | ~ m1_subset_1(B_118,k1_zfmisc_1(A_117)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_612,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_595])).

tff(c_8,plain,(
    ! [A_7,C_9,B_8] :
      ( r1_xboole_0(A_7,C_9)
      | ~ r1_tarski(A_7,k4_xboole_0(B_8,C_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1598,plain,(
    ! [A_185] :
      ( r1_xboole_0(A_185,'#skF_4')
      | ~ r1_tarski(A_185,k3_subset_1('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_612,c_8])).

tff(c_1679,plain,(
    r1_xboole_0(k3_subset_1('#skF_3','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_191,c_1598])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1688,plain,(
    r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_1679,c_4])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_611,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_595])).

tff(c_20,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k4_xboole_0(A_20,B_21)) = k3_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_835,plain,(
    ! [A_130,B_131,C_132] :
      ( r1_tarski(A_130,k4_xboole_0(B_131,C_132))
      | ~ r1_xboole_0(A_130,C_132)
      | ~ r1_tarski(A_130,B_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2834,plain,(
    ! [A_230,A_231,B_232] :
      ( r1_tarski(A_230,k3_xboole_0(A_231,B_232))
      | ~ r1_xboole_0(A_230,k4_xboole_0(A_231,B_232))
      | ~ r1_tarski(A_230,A_231) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_835])).

tff(c_12333,plain,(
    ! [A_644] :
      ( r1_tarski(A_644,k3_xboole_0('#skF_3','#skF_5'))
      | ~ r1_xboole_0(A_644,k3_subset_1('#skF_3','#skF_5'))
      | ~ r1_tarski(A_644,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_611,c_2834])).

tff(c_12399,plain,
    ( r1_tarski('#skF_4',k3_xboole_0('#skF_3','#skF_5'))
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_1688,c_12333])).

tff(c_12449,plain,(
    r1_tarski('#skF_4',k3_xboole_0('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_12399])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_425,plain,(
    ! [A_98,B_99,C_100] :
      ( r1_tarski(A_98,B_99)
      | ~ r1_tarski(A_98,k4_xboole_0(B_99,C_100)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1271,plain,(
    ! [A_169,A_170,B_171] :
      ( r1_tarski(A_169,A_170)
      | ~ r1_tarski(A_169,k3_xboole_0(A_170,B_171)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_425])).

tff(c_1333,plain,(
    ! [A_169,B_2,A_1] :
      ( r1_tarski(A_169,B_2)
      | ~ r1_tarski(A_169,k3_xboole_0(A_1,B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1271])).

tff(c_12465,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_12449,c_1333])).

tff(c_12476,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_12465])).

tff(c_12477,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_12478,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_13083,plain,(
    ! [A_730,B_731] :
      ( k4_xboole_0(A_730,B_731) = k3_subset_1(A_730,B_731)
      | ~ m1_subset_1(B_731,k1_zfmisc_1(A_730)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_13099,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_13083])).

tff(c_13100,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_13083])).

tff(c_16,plain,(
    ! [C_17,B_16,A_15] :
      ( r1_tarski(k4_xboole_0(C_17,B_16),k4_xboole_0(C_17,A_15))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_16170,plain,(
    ! [B_863] :
      ( r1_tarski(k4_xboole_0('#skF_3',B_863),k3_subset_1('#skF_3','#skF_4'))
      | ~ r1_tarski('#skF_4',B_863) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13100,c_16])).

tff(c_16195,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4'))
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_13099,c_16170])).

tff(c_16205,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12478,c_16195])).

tff(c_16207,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12477,c_16205])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 12:28:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.91/4.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.91/4.41  
% 10.91/4.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.91/4.41  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 10.91/4.41  
% 10.91/4.41  %Foreground sorts:
% 10.91/4.41  
% 10.91/4.41  
% 10.91/4.41  %Background operators:
% 10.91/4.41  
% 10.91/4.41  
% 10.91/4.41  %Foreground operators:
% 10.91/4.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.91/4.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.91/4.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.91/4.41  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.91/4.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.91/4.41  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 10.91/4.41  tff('#skF_5', type, '#skF_5': $i).
% 10.91/4.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.91/4.41  tff('#skF_3', type, '#skF_3': $i).
% 10.91/4.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.91/4.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.91/4.41  tff('#skF_4', type, '#skF_4': $i).
% 10.91/4.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.91/4.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 10.91/4.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.91/4.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.91/4.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.91/4.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.91/4.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.91/4.41  
% 11.11/4.43  tff(f_98, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 11.11/4.43  tff(f_88, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 11.11/4.43  tff(f_81, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 11.11/4.43  tff(f_68, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 11.11/4.43  tff(f_85, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 11.11/4.43  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 11.11/4.43  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 11.11/4.43  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 11.11/4.43  tff(f_61, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 11.11/4.43  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 11.11/4.43  tff(f_51, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(C, B), k4_xboole_0(C, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_xboole_1)).
% 11.11/4.43  tff(c_52, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_98])).
% 11.11/4.43  tff(c_110, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_52])).
% 11.11/4.43  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 11.11/4.43  tff(c_46, plain, (![A_34]: (~v1_xboole_0(k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.11/4.43  tff(c_241, plain, (![B_67, A_68]: (r2_hidden(B_67, A_68) | ~m1_subset_1(B_67, A_68) | v1_xboole_0(A_68))), inference(cnfTransformation, [status(thm)], [f_81])).
% 11.11/4.43  tff(c_24, plain, (![C_29, A_25]: (r1_tarski(C_29, A_25) | ~r2_hidden(C_29, k1_zfmisc_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 11.11/4.43  tff(c_245, plain, (![B_67, A_25]: (r1_tarski(B_67, A_25) | ~m1_subset_1(B_67, k1_zfmisc_1(A_25)) | v1_xboole_0(k1_zfmisc_1(A_25)))), inference(resolution, [status(thm)], [c_241, c_24])).
% 11.11/4.43  tff(c_249, plain, (![B_69, A_70]: (r1_tarski(B_69, A_70) | ~m1_subset_1(B_69, k1_zfmisc_1(A_70)))), inference(negUnitSimplification, [status(thm)], [c_46, c_245])).
% 11.11/4.43  tff(c_262, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_249])).
% 11.11/4.43  tff(c_58, plain, (r1_tarski('#skF_4', '#skF_5') | r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 11.11/4.43  tff(c_191, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_110, c_58])).
% 11.11/4.43  tff(c_595, plain, (![A_117, B_118]: (k4_xboole_0(A_117, B_118)=k3_subset_1(A_117, B_118) | ~m1_subset_1(B_118, k1_zfmisc_1(A_117)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 11.11/4.43  tff(c_612, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_595])).
% 11.11/4.43  tff(c_8, plain, (![A_7, C_9, B_8]: (r1_xboole_0(A_7, C_9) | ~r1_tarski(A_7, k4_xboole_0(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.11/4.43  tff(c_1598, plain, (![A_185]: (r1_xboole_0(A_185, '#skF_4') | ~r1_tarski(A_185, k3_subset_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_612, c_8])).
% 11.11/4.43  tff(c_1679, plain, (r1_xboole_0(k3_subset_1('#skF_3', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_191, c_1598])).
% 11.11/4.43  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.11/4.43  tff(c_1688, plain, (r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_1679, c_4])).
% 11.11/4.43  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 11.11/4.43  tff(c_611, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_48, c_595])).
% 11.11/4.43  tff(c_20, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k4_xboole_0(A_20, B_21))=k3_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.11/4.43  tff(c_835, plain, (![A_130, B_131, C_132]: (r1_tarski(A_130, k4_xboole_0(B_131, C_132)) | ~r1_xboole_0(A_130, C_132) | ~r1_tarski(A_130, B_131))), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.11/4.43  tff(c_2834, plain, (![A_230, A_231, B_232]: (r1_tarski(A_230, k3_xboole_0(A_231, B_232)) | ~r1_xboole_0(A_230, k4_xboole_0(A_231, B_232)) | ~r1_tarski(A_230, A_231))), inference(superposition, [status(thm), theory('equality')], [c_20, c_835])).
% 11.11/4.43  tff(c_12333, plain, (![A_644]: (r1_tarski(A_644, k3_xboole_0('#skF_3', '#skF_5')) | ~r1_xboole_0(A_644, k3_subset_1('#skF_3', '#skF_5')) | ~r1_tarski(A_644, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_611, c_2834])).
% 11.11/4.43  tff(c_12399, plain, (r1_tarski('#skF_4', k3_xboole_0('#skF_3', '#skF_5')) | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_1688, c_12333])).
% 11.11/4.43  tff(c_12449, plain, (r1_tarski('#skF_4', k3_xboole_0('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_262, c_12399])).
% 11.11/4.43  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.11/4.43  tff(c_425, plain, (![A_98, B_99, C_100]: (r1_tarski(A_98, B_99) | ~r1_tarski(A_98, k4_xboole_0(B_99, C_100)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.11/4.43  tff(c_1271, plain, (![A_169, A_170, B_171]: (r1_tarski(A_169, A_170) | ~r1_tarski(A_169, k3_xboole_0(A_170, B_171)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_425])).
% 11.11/4.43  tff(c_1333, plain, (![A_169, B_2, A_1]: (r1_tarski(A_169, B_2) | ~r1_tarski(A_169, k3_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1271])).
% 11.11/4.43  tff(c_12465, plain, (r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_12449, c_1333])).
% 11.11/4.43  tff(c_12476, plain, $false, inference(negUnitSimplification, [status(thm)], [c_110, c_12465])).
% 11.11/4.43  tff(c_12477, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_52])).
% 11.11/4.43  tff(c_12478, plain, (r1_tarski('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_52])).
% 11.11/4.43  tff(c_13083, plain, (![A_730, B_731]: (k4_xboole_0(A_730, B_731)=k3_subset_1(A_730, B_731) | ~m1_subset_1(B_731, k1_zfmisc_1(A_730)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 11.11/4.43  tff(c_13099, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_48, c_13083])).
% 11.11/4.43  tff(c_13100, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_13083])).
% 11.11/4.43  tff(c_16, plain, (![C_17, B_16, A_15]: (r1_tarski(k4_xboole_0(C_17, B_16), k4_xboole_0(C_17, A_15)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.11/4.43  tff(c_16170, plain, (![B_863]: (r1_tarski(k4_xboole_0('#skF_3', B_863), k3_subset_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_4', B_863))), inference(superposition, [status(thm), theory('equality')], [c_13100, c_16])).
% 11.11/4.43  tff(c_16195, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_13099, c_16170])).
% 11.11/4.43  tff(c_16205, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_12478, c_16195])).
% 11.11/4.43  tff(c_16207, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12477, c_16205])).
% 11.11/4.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.11/4.43  
% 11.11/4.43  Inference rules
% 11.11/4.43  ----------------------
% 11.11/4.43  #Ref     : 0
% 11.11/4.43  #Sup     : 3731
% 11.11/4.43  #Fact    : 0
% 11.11/4.43  #Define  : 0
% 11.11/4.43  #Split   : 7
% 11.11/4.43  #Chain   : 0
% 11.11/4.43  #Close   : 0
% 11.11/4.43  
% 11.11/4.43  Ordering : KBO
% 11.11/4.43  
% 11.11/4.43  Simplification rules
% 11.11/4.43  ----------------------
% 11.11/4.43  #Subsume      : 123
% 11.11/4.43  #Demod        : 1329
% 11.11/4.43  #Tautology    : 1539
% 11.11/4.43  #SimpNegUnit  : 12
% 11.11/4.43  #BackRed      : 0
% 11.11/4.43  
% 11.11/4.43  #Partial instantiations: 0
% 11.11/4.43  #Strategies tried      : 1
% 11.11/4.43  
% 11.11/4.43  Timing (in seconds)
% 11.11/4.43  ----------------------
% 11.11/4.43  Preprocessing        : 0.39
% 11.11/4.43  Parsing              : 0.20
% 11.11/4.43  CNF conversion       : 0.03
% 11.11/4.43  Main loop            : 3.18
% 11.11/4.43  Inferencing          : 0.77
% 11.11/4.43  Reduction            : 1.42
% 11.11/4.43  Demodulation         : 1.17
% 11.11/4.43  BG Simplification    : 0.08
% 11.11/4.43  Subsumption          : 0.66
% 11.11/4.43  Abstraction          : 0.09
% 11.11/4.43  MUC search           : 0.00
% 11.11/4.43  Cooper               : 0.00
% 11.11/4.43  Total                : 3.60
% 11.11/4.43  Index Insertion      : 0.00
% 11.11/4.43  Index Deletion       : 0.00
% 11.11/4.43  Index Matching       : 0.00
% 11.11/4.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
