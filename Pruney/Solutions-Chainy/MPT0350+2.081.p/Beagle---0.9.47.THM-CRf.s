%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:36 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 103 expanded)
%              Number of leaves         :   31 (  49 expanded)
%              Depth                    :    8
%              Number of atoms          :   84 ( 158 expanded)
%              Number of equality atoms :   23 (  41 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_57,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_79,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_68,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_30,plain,(
    ! [A_16] : k2_subset_1(A_16) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_40,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_43,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_40])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_36,plain,(
    ! [A_21] : ~ v1_xboole_0(k1_zfmisc_1(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_100,plain,(
    ! [B_43,A_44] :
      ( r2_hidden(B_43,A_44)
      | ~ m1_subset_1(B_43,A_44)
      | v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_8,plain,(
    ! [C_11,A_7] :
      ( r1_tarski(C_11,A_7)
      | ~ r2_hidden(C_11,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_107,plain,(
    ! [B_43,A_7] :
      ( r1_tarski(B_43,A_7)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_7))
      | v1_xboole_0(k1_zfmisc_1(A_7)) ) ),
    inference(resolution,[status(thm)],[c_100,c_8])).

tff(c_112,plain,(
    ! [B_45,A_46] :
      ( r1_tarski(B_45,A_46)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_46)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_107])).

tff(c_125,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_112])).

tff(c_144,plain,(
    ! [A_51,B_52] :
      ( k4_xboole_0(A_51,B_52) = k3_subset_1(A_51,B_52)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_157,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_144])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = B_4
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_161,plain,
    ( k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_4])).

tff(c_165,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_161])).

tff(c_177,plain,(
    ! [A_55,B_56] :
      ( m1_subset_1(k3_subset_1(A_55,B_56),k1_zfmisc_1(A_55))
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_111,plain,(
    ! [B_43,A_7] :
      ( r1_tarski(B_43,A_7)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_7)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_107])).

tff(c_188,plain,(
    ! [A_55,B_56] :
      ( r1_tarski(k3_subset_1(A_55,B_56),A_55)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_55)) ) ),
    inference(resolution,[status(thm)],[c_177,c_111])).

tff(c_32,plain,(
    ! [A_17,B_18] :
      ( k4_xboole_0(A_17,B_18) = k3_subset_1(A_17,B_18)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_229,plain,(
    ! [A_67,B_68] :
      ( k4_xboole_0(A_67,k3_subset_1(A_67,B_68)) = k3_subset_1(A_67,k3_subset_1(A_67,B_68))
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_67)) ) ),
    inference(resolution,[status(thm)],[c_177,c_32])).

tff(c_242,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = k3_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_42,c_229])).

tff(c_246,plain,
    ( k2_xboole_0(k3_subset_1('#skF_3','#skF_4'),k3_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_4'))) = '#skF_3'
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_4])).

tff(c_250,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_246])).

tff(c_253,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_188,c_250])).

tff(c_257,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_253])).

tff(c_259,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_246])).

tff(c_10,plain,(
    ! [C_11,A_7] :
      ( r2_hidden(C_11,k1_zfmisc_1(A_7))
      | ~ r1_tarski(C_11,A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_88,plain,(
    ! [B_39,A_40] :
      ( m1_subset_1(B_39,A_40)
      | ~ r2_hidden(B_39,A_40)
      | v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_91,plain,(
    ! [C_11,A_7] :
      ( m1_subset_1(C_11,k1_zfmisc_1(A_7))
      | v1_xboole_0(k1_zfmisc_1(A_7))
      | ~ r1_tarski(C_11,A_7) ) ),
    inference(resolution,[status(thm)],[c_10,c_88])).

tff(c_94,plain,(
    ! [C_11,A_7] :
      ( m1_subset_1(C_11,k1_zfmisc_1(A_7))
      | ~ r1_tarski(C_11,A_7) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_91])).

tff(c_293,plain,(
    ! [A_71,B_72,C_73] :
      ( k4_subset_1(A_71,B_72,C_73) = k2_xboole_0(B_72,C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(A_71))
      | ~ m1_subset_1(B_72,k1_zfmisc_1(A_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_373,plain,(
    ! [A_77,B_78,C_79] :
      ( k4_subset_1(A_77,B_78,C_79) = k2_xboole_0(B_78,C_79)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_77))
      | ~ r1_tarski(C_79,A_77) ) ),
    inference(resolution,[status(thm)],[c_94,c_293])).

tff(c_387,plain,(
    ! [C_80] :
      ( k4_subset_1('#skF_3','#skF_4',C_80) = k2_xboole_0('#skF_4',C_80)
      | ~ r1_tarski(C_80,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_42,c_373])).

tff(c_390,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_259,c_387])).

tff(c_401,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_390])).

tff(c_403,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_401])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:37:10 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.37/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.31  
% 2.37/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.31  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.37/1.31  
% 2.37/1.31  %Foreground sorts:
% 2.37/1.31  
% 2.37/1.31  
% 2.37/1.31  %Background operators:
% 2.37/1.31  
% 2.37/1.31  
% 2.37/1.31  %Foreground operators:
% 2.37/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.37/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.37/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.37/1.31  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.37/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.37/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.37/1.31  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.37/1.31  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.37/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.37/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.37/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.37/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.37/1.31  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.37/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.37/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.37/1.31  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.37/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.37/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.37/1.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.37/1.31  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.37/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.37/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.37/1.31  
% 2.37/1.32  tff(f_57, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.37/1.32  tff(f_79, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 2.37/1.32  tff(f_68, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.37/1.32  tff(f_55, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.37/1.32  tff(f_40, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.37/1.32  tff(f_61, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.37/1.32  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_xboole_1)).
% 2.37/1.32  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.37/1.32  tff(f_74, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.37/1.32  tff(c_30, plain, (![A_16]: (k2_subset_1(A_16)=A_16)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.37/1.32  tff(c_40, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.37/1.32  tff(c_43, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_40])).
% 2.37/1.32  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.37/1.32  tff(c_36, plain, (![A_21]: (~v1_xboole_0(k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.37/1.32  tff(c_100, plain, (![B_43, A_44]: (r2_hidden(B_43, A_44) | ~m1_subset_1(B_43, A_44) | v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.37/1.32  tff(c_8, plain, (![C_11, A_7]: (r1_tarski(C_11, A_7) | ~r2_hidden(C_11, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.37/1.32  tff(c_107, plain, (![B_43, A_7]: (r1_tarski(B_43, A_7) | ~m1_subset_1(B_43, k1_zfmisc_1(A_7)) | v1_xboole_0(k1_zfmisc_1(A_7)))), inference(resolution, [status(thm)], [c_100, c_8])).
% 2.37/1.32  tff(c_112, plain, (![B_45, A_46]: (r1_tarski(B_45, A_46) | ~m1_subset_1(B_45, k1_zfmisc_1(A_46)))), inference(negUnitSimplification, [status(thm)], [c_36, c_107])).
% 2.37/1.32  tff(c_125, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_112])).
% 2.37/1.32  tff(c_144, plain, (![A_51, B_52]: (k4_xboole_0(A_51, B_52)=k3_subset_1(A_51, B_52) | ~m1_subset_1(B_52, k1_zfmisc_1(A_51)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.37/1.32  tff(c_157, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_144])).
% 2.37/1.32  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k4_xboole_0(B_4, A_3))=B_4 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.37/1.32  tff(c_161, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3' | ~r1_tarski('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_157, c_4])).
% 2.37/1.32  tff(c_165, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_125, c_161])).
% 2.37/1.32  tff(c_177, plain, (![A_55, B_56]: (m1_subset_1(k3_subset_1(A_55, B_56), k1_zfmisc_1(A_55)) | ~m1_subset_1(B_56, k1_zfmisc_1(A_55)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.37/1.32  tff(c_111, plain, (![B_43, A_7]: (r1_tarski(B_43, A_7) | ~m1_subset_1(B_43, k1_zfmisc_1(A_7)))), inference(negUnitSimplification, [status(thm)], [c_36, c_107])).
% 2.37/1.32  tff(c_188, plain, (![A_55, B_56]: (r1_tarski(k3_subset_1(A_55, B_56), A_55) | ~m1_subset_1(B_56, k1_zfmisc_1(A_55)))), inference(resolution, [status(thm)], [c_177, c_111])).
% 2.37/1.32  tff(c_32, plain, (![A_17, B_18]: (k4_xboole_0(A_17, B_18)=k3_subset_1(A_17, B_18) | ~m1_subset_1(B_18, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.37/1.32  tff(c_229, plain, (![A_67, B_68]: (k4_xboole_0(A_67, k3_subset_1(A_67, B_68))=k3_subset_1(A_67, k3_subset_1(A_67, B_68)) | ~m1_subset_1(B_68, k1_zfmisc_1(A_67)))), inference(resolution, [status(thm)], [c_177, c_32])).
% 2.37/1.32  tff(c_242, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))=k3_subset_1('#skF_3', k3_subset_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_42, c_229])).
% 2.37/1.32  tff(c_246, plain, (k2_xboole_0(k3_subset_1('#skF_3', '#skF_4'), k3_subset_1('#skF_3', k3_subset_1('#skF_3', '#skF_4')))='#skF_3' | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_242, c_4])).
% 2.37/1.32  tff(c_250, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_246])).
% 2.37/1.32  tff(c_253, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_188, c_250])).
% 2.37/1.32  tff(c_257, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_253])).
% 2.37/1.32  tff(c_259, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_246])).
% 2.37/1.32  tff(c_10, plain, (![C_11, A_7]: (r2_hidden(C_11, k1_zfmisc_1(A_7)) | ~r1_tarski(C_11, A_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.37/1.32  tff(c_88, plain, (![B_39, A_40]: (m1_subset_1(B_39, A_40) | ~r2_hidden(B_39, A_40) | v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.37/1.32  tff(c_91, plain, (![C_11, A_7]: (m1_subset_1(C_11, k1_zfmisc_1(A_7)) | v1_xboole_0(k1_zfmisc_1(A_7)) | ~r1_tarski(C_11, A_7))), inference(resolution, [status(thm)], [c_10, c_88])).
% 2.37/1.32  tff(c_94, plain, (![C_11, A_7]: (m1_subset_1(C_11, k1_zfmisc_1(A_7)) | ~r1_tarski(C_11, A_7))), inference(negUnitSimplification, [status(thm)], [c_36, c_91])).
% 2.37/1.32  tff(c_293, plain, (![A_71, B_72, C_73]: (k4_subset_1(A_71, B_72, C_73)=k2_xboole_0(B_72, C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(A_71)) | ~m1_subset_1(B_72, k1_zfmisc_1(A_71)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.37/1.32  tff(c_373, plain, (![A_77, B_78, C_79]: (k4_subset_1(A_77, B_78, C_79)=k2_xboole_0(B_78, C_79) | ~m1_subset_1(B_78, k1_zfmisc_1(A_77)) | ~r1_tarski(C_79, A_77))), inference(resolution, [status(thm)], [c_94, c_293])).
% 2.37/1.32  tff(c_387, plain, (![C_80]: (k4_subset_1('#skF_3', '#skF_4', C_80)=k2_xboole_0('#skF_4', C_80) | ~r1_tarski(C_80, '#skF_3'))), inference(resolution, [status(thm)], [c_42, c_373])).
% 2.37/1.32  tff(c_390, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_259, c_387])).
% 2.37/1.32  tff(c_401, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_165, c_390])).
% 2.37/1.32  tff(c_403, plain, $false, inference(negUnitSimplification, [status(thm)], [c_43, c_401])).
% 2.37/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.32  
% 2.37/1.32  Inference rules
% 2.37/1.32  ----------------------
% 2.37/1.32  #Ref     : 0
% 2.37/1.32  #Sup     : 82
% 2.37/1.32  #Fact    : 0
% 2.37/1.32  #Define  : 0
% 2.37/1.32  #Split   : 1
% 2.37/1.32  #Chain   : 0
% 2.37/1.32  #Close   : 0
% 2.37/1.32  
% 2.37/1.32  Ordering : KBO
% 2.37/1.32  
% 2.37/1.32  Simplification rules
% 2.37/1.32  ----------------------
% 2.37/1.32  #Subsume      : 11
% 2.37/1.32  #Demod        : 10
% 2.37/1.32  #Tautology    : 34
% 2.37/1.32  #SimpNegUnit  : 3
% 2.37/1.32  #BackRed      : 0
% 2.37/1.32  
% 2.37/1.32  #Partial instantiations: 0
% 2.37/1.32  #Strategies tried      : 1
% 2.37/1.32  
% 2.37/1.32  Timing (in seconds)
% 2.37/1.32  ----------------------
% 2.37/1.33  Preprocessing        : 0.32
% 2.37/1.33  Parsing              : 0.16
% 2.37/1.33  CNF conversion       : 0.02
% 2.37/1.33  Main loop            : 0.26
% 2.37/1.33  Inferencing          : 0.10
% 2.37/1.33  Reduction            : 0.07
% 2.37/1.33  Demodulation         : 0.05
% 2.37/1.33  BG Simplification    : 0.02
% 2.37/1.33  Subsumption          : 0.05
% 2.37/1.33  Abstraction          : 0.02
% 2.37/1.33  MUC search           : 0.00
% 2.37/1.33  Cooper               : 0.00
% 2.37/1.33  Total                : 0.61
% 2.37/1.33  Index Insertion      : 0.00
% 2.37/1.33  Index Deletion       : 0.00
% 2.37/1.33  Index Matching       : 0.00
% 2.37/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
