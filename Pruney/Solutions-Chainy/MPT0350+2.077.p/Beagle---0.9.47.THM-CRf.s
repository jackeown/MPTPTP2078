%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:35 EST 2020

% Result     : Theorem 2.54s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :   66 (  84 expanded)
%              Number of leaves         :   33 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :   80 ( 121 expanded)
%              Number of equality atoms :   26 (  32 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_61,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_83,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_72,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_34,plain,(
    ! [A_20] : k2_subset_1(A_20) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_44,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_47,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_44])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_40,plain,(
    ! [A_25] : ~ v1_xboole_0(k1_zfmisc_1(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_141,plain,(
    ! [B_49,A_50] :
      ( r2_hidden(B_49,A_50)
      | ~ m1_subset_1(B_49,A_50)
      | v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_12,plain,(
    ! [C_15,A_11] :
      ( r1_tarski(C_15,A_11)
      | ~ r2_hidden(C_15,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_145,plain,(
    ! [B_49,A_11] :
      ( r1_tarski(B_49,A_11)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_11))
      | v1_xboole_0(k1_zfmisc_1(A_11)) ) ),
    inference(resolution,[status(thm)],[c_141,c_12])).

tff(c_149,plain,(
    ! [B_51,A_52] :
      ( r1_tarski(B_51,A_52)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_52)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_145])).

tff(c_158,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_149])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_177,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_158,c_6])).

tff(c_251,plain,(
    ! [A_61,B_62] :
      ( k4_xboole_0(A_61,B_62) = k3_subset_1(A_61,B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_264,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_251])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_126,plain,(
    ! [A_47,B_48] : k2_xboole_0(k3_xboole_0(A_47,B_48),k4_xboole_0(A_47,B_48)) = A_47 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_135,plain,(
    ! [B_2,A_1] : k2_xboole_0(k3_xboole_0(B_2,A_1),k4_xboole_0(A_1,B_2)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_126])).

tff(c_269,plain,(
    k2_xboole_0(k3_xboole_0('#skF_4','#skF_3'),k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_135])).

tff(c_275,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_269])).

tff(c_326,plain,(
    ! [A_67,B_68] :
      ( m1_subset_1(k3_subset_1(A_67,B_68),k1_zfmisc_1(A_67))
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_148,plain,(
    ! [B_49,A_11] :
      ( r1_tarski(B_49,A_11)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_11)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_145])).

tff(c_337,plain,(
    ! [A_67,B_68] :
      ( r1_tarski(k3_subset_1(A_67,B_68),A_67)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_67)) ) ),
    inference(resolution,[status(thm)],[c_326,c_148])).

tff(c_14,plain,(
    ! [C_15,A_11] :
      ( r2_hidden(C_15,k1_zfmisc_1(A_11))
      | ~ r1_tarski(C_15,A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_196,plain,(
    ! [B_55,A_56] :
      ( m1_subset_1(B_55,A_56)
      | ~ r2_hidden(B_55,A_56)
      | v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_202,plain,(
    ! [C_15,A_11] :
      ( m1_subset_1(C_15,k1_zfmisc_1(A_11))
      | v1_xboole_0(k1_zfmisc_1(A_11))
      | ~ r1_tarski(C_15,A_11) ) ),
    inference(resolution,[status(thm)],[c_14,c_196])).

tff(c_206,plain,(
    ! [C_15,A_11] :
      ( m1_subset_1(C_15,k1_zfmisc_1(A_11))
      | ~ r1_tarski(C_15,A_11) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_202])).

tff(c_509,plain,(
    ! [A_87,B_88,C_89] :
      ( k4_subset_1(A_87,B_88,C_89) = k2_xboole_0(B_88,C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(A_87))
      | ~ m1_subset_1(B_88,k1_zfmisc_1(A_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_682,plain,(
    ! [A_99,B_100,C_101] :
      ( k4_subset_1(A_99,B_100,C_101) = k2_xboole_0(B_100,C_101)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(A_99))
      | ~ r1_tarski(C_101,A_99) ) ),
    inference(resolution,[status(thm)],[c_206,c_509])).

tff(c_697,plain,(
    ! [C_104] :
      ( k4_subset_1('#skF_3','#skF_4',C_104) = k2_xboole_0('#skF_4',C_104)
      | ~ r1_tarski(C_104,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_46,c_682])).

tff(c_741,plain,(
    ! [B_109] :
      ( k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3',B_109)) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3',B_109))
      | ~ m1_subset_1(B_109,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_337,c_697])).

tff(c_756,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_46,c_741])).

tff(c_761,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_756])).

tff(c_763,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_761])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.31  % Computer   : n015.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 11:05:08 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.17/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.54/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.32  
% 2.54/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.32  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.54/1.32  
% 2.54/1.32  %Foreground sorts:
% 2.54/1.32  
% 2.54/1.32  
% 2.54/1.32  %Background operators:
% 2.54/1.32  
% 2.54/1.32  
% 2.54/1.32  %Foreground operators:
% 2.54/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.54/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.54/1.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.54/1.32  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.54/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.54/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.54/1.32  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.54/1.32  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.54/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.54/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.54/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.54/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.54/1.32  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.54/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.54/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.54/1.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.54/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.54/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.54/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.54/1.32  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.54/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.54/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.54/1.32  
% 2.83/1.33  tff(f_61, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.83/1.33  tff(f_83, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 2.83/1.33  tff(f_72, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.83/1.33  tff(f_59, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.83/1.33  tff(f_44, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.83/1.33  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.83/1.33  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.83/1.33  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.83/1.33  tff(f_35, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 2.83/1.33  tff(f_69, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.83/1.33  tff(f_78, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.83/1.33  tff(c_34, plain, (![A_20]: (k2_subset_1(A_20)=A_20)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.83/1.33  tff(c_44, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.83/1.33  tff(c_47, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_44])).
% 2.83/1.33  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.83/1.33  tff(c_40, plain, (![A_25]: (~v1_xboole_0(k1_zfmisc_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.83/1.33  tff(c_141, plain, (![B_49, A_50]: (r2_hidden(B_49, A_50) | ~m1_subset_1(B_49, A_50) | v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.83/1.33  tff(c_12, plain, (![C_15, A_11]: (r1_tarski(C_15, A_11) | ~r2_hidden(C_15, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.83/1.33  tff(c_145, plain, (![B_49, A_11]: (r1_tarski(B_49, A_11) | ~m1_subset_1(B_49, k1_zfmisc_1(A_11)) | v1_xboole_0(k1_zfmisc_1(A_11)))), inference(resolution, [status(thm)], [c_141, c_12])).
% 2.83/1.33  tff(c_149, plain, (![B_51, A_52]: (r1_tarski(B_51, A_52) | ~m1_subset_1(B_51, k1_zfmisc_1(A_52)))), inference(negUnitSimplification, [status(thm)], [c_40, c_145])).
% 2.83/1.33  tff(c_158, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_149])).
% 2.83/1.33  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.83/1.33  tff(c_177, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_158, c_6])).
% 2.83/1.33  tff(c_251, plain, (![A_61, B_62]: (k4_xboole_0(A_61, B_62)=k3_subset_1(A_61, B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.83/1.33  tff(c_264, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_251])).
% 2.83/1.33  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.83/1.33  tff(c_126, plain, (![A_47, B_48]: (k2_xboole_0(k3_xboole_0(A_47, B_48), k4_xboole_0(A_47, B_48))=A_47)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.83/1.33  tff(c_135, plain, (![B_2, A_1]: (k2_xboole_0(k3_xboole_0(B_2, A_1), k4_xboole_0(A_1, B_2))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_126])).
% 2.83/1.33  tff(c_269, plain, (k2_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_264, c_135])).
% 2.83/1.33  tff(c_275, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_177, c_269])).
% 2.83/1.33  tff(c_326, plain, (![A_67, B_68]: (m1_subset_1(k3_subset_1(A_67, B_68), k1_zfmisc_1(A_67)) | ~m1_subset_1(B_68, k1_zfmisc_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.83/1.33  tff(c_148, plain, (![B_49, A_11]: (r1_tarski(B_49, A_11) | ~m1_subset_1(B_49, k1_zfmisc_1(A_11)))), inference(negUnitSimplification, [status(thm)], [c_40, c_145])).
% 2.83/1.33  tff(c_337, plain, (![A_67, B_68]: (r1_tarski(k3_subset_1(A_67, B_68), A_67) | ~m1_subset_1(B_68, k1_zfmisc_1(A_67)))), inference(resolution, [status(thm)], [c_326, c_148])).
% 2.83/1.33  tff(c_14, plain, (![C_15, A_11]: (r2_hidden(C_15, k1_zfmisc_1(A_11)) | ~r1_tarski(C_15, A_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.83/1.33  tff(c_196, plain, (![B_55, A_56]: (m1_subset_1(B_55, A_56) | ~r2_hidden(B_55, A_56) | v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.83/1.33  tff(c_202, plain, (![C_15, A_11]: (m1_subset_1(C_15, k1_zfmisc_1(A_11)) | v1_xboole_0(k1_zfmisc_1(A_11)) | ~r1_tarski(C_15, A_11))), inference(resolution, [status(thm)], [c_14, c_196])).
% 2.83/1.33  tff(c_206, plain, (![C_15, A_11]: (m1_subset_1(C_15, k1_zfmisc_1(A_11)) | ~r1_tarski(C_15, A_11))), inference(negUnitSimplification, [status(thm)], [c_40, c_202])).
% 2.83/1.33  tff(c_509, plain, (![A_87, B_88, C_89]: (k4_subset_1(A_87, B_88, C_89)=k2_xboole_0(B_88, C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(A_87)) | ~m1_subset_1(B_88, k1_zfmisc_1(A_87)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.83/1.33  tff(c_682, plain, (![A_99, B_100, C_101]: (k4_subset_1(A_99, B_100, C_101)=k2_xboole_0(B_100, C_101) | ~m1_subset_1(B_100, k1_zfmisc_1(A_99)) | ~r1_tarski(C_101, A_99))), inference(resolution, [status(thm)], [c_206, c_509])).
% 2.83/1.33  tff(c_697, plain, (![C_104]: (k4_subset_1('#skF_3', '#skF_4', C_104)=k2_xboole_0('#skF_4', C_104) | ~r1_tarski(C_104, '#skF_3'))), inference(resolution, [status(thm)], [c_46, c_682])).
% 2.83/1.33  tff(c_741, plain, (![B_109]: (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', B_109))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', B_109)) | ~m1_subset_1(B_109, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_337, c_697])).
% 2.83/1.33  tff(c_756, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_46, c_741])).
% 2.83/1.33  tff(c_761, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_275, c_756])).
% 2.83/1.33  tff(c_763, plain, $false, inference(negUnitSimplification, [status(thm)], [c_47, c_761])).
% 2.83/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.33  
% 2.83/1.33  Inference rules
% 2.83/1.33  ----------------------
% 2.83/1.33  #Ref     : 0
% 2.83/1.33  #Sup     : 175
% 2.83/1.33  #Fact    : 0
% 2.83/1.33  #Define  : 0
% 2.83/1.33  #Split   : 0
% 2.83/1.33  #Chain   : 0
% 2.83/1.33  #Close   : 0
% 2.83/1.33  
% 2.83/1.33  Ordering : KBO
% 2.83/1.33  
% 2.83/1.33  Simplification rules
% 2.83/1.33  ----------------------
% 2.83/1.33  #Subsume      : 13
% 2.83/1.33  #Demod        : 44
% 2.83/1.33  #Tautology    : 100
% 2.83/1.33  #SimpNegUnit  : 4
% 2.83/1.33  #BackRed      : 3
% 2.83/1.33  
% 2.83/1.33  #Partial instantiations: 0
% 2.83/1.33  #Strategies tried      : 1
% 2.83/1.33  
% 2.83/1.33  Timing (in seconds)
% 2.83/1.33  ----------------------
% 2.83/1.34  Preprocessing        : 0.32
% 2.83/1.34  Parsing              : 0.17
% 2.83/1.34  CNF conversion       : 0.02
% 2.83/1.34  Main loop            : 0.31
% 2.83/1.34  Inferencing          : 0.12
% 2.83/1.34  Reduction            : 0.10
% 2.83/1.34  Demodulation         : 0.07
% 2.83/1.34  BG Simplification    : 0.02
% 2.83/1.34  Subsumption          : 0.05
% 2.83/1.34  Abstraction          : 0.02
% 2.83/1.34  MUC search           : 0.00
% 2.83/1.34  Cooper               : 0.00
% 2.83/1.34  Total                : 0.66
% 2.83/1.34  Index Insertion      : 0.00
% 2.83/1.34  Index Deletion       : 0.00
% 2.83/1.34  Index Matching       : 0.00
% 2.83/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
