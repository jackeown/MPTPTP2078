%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:30 EST 2020

% Result     : Theorem 2.40s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :   63 (  81 expanded)
%              Number of leaves         :   32 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :   77 ( 118 expanded)
%              Number of equality atoms :   23 (  29 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_83,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_72,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

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

tff(c_135,plain,(
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

tff(c_139,plain,(
    ! [B_49,A_11] :
      ( r1_tarski(B_49,A_11)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_11))
      | v1_xboole_0(k1_zfmisc_1(A_11)) ) ),
    inference(resolution,[status(thm)],[c_135,c_12])).

tff(c_143,plain,(
    ! [B_51,A_52] :
      ( r1_tarski(B_51,A_52)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_52)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_139])).

tff(c_152,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_143])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k2_xboole_0(A_5,B_6) = B_6
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_165,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_152,c_6])).

tff(c_181,plain,(
    ! [A_57,B_58] :
      ( k4_xboole_0(A_57,B_58) = k3_subset_1(A_57,B_58)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_190,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_181])).

tff(c_8,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k4_xboole_0(B_8,A_7)) = k2_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_194,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_8])).

tff(c_197,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_194])).

tff(c_222,plain,(
    ! [A_63,B_64] :
      ( m1_subset_1(k3_subset_1(A_63,B_64),k1_zfmisc_1(A_63))
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_142,plain,(
    ! [B_49,A_11] :
      ( r1_tarski(B_49,A_11)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_11)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_139])).

tff(c_233,plain,(
    ! [A_63,B_64] :
      ( r1_tarski(k3_subset_1(A_63,B_64),A_63)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_63)) ) ),
    inference(resolution,[status(thm)],[c_222,c_142])).

tff(c_14,plain,(
    ! [C_15,A_11] :
      ( r2_hidden(C_15,k1_zfmisc_1(A_11))
      | ~ r1_tarski(C_15,A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_170,plain,(
    ! [B_55,A_56] :
      ( m1_subset_1(B_55,A_56)
      | ~ r2_hidden(B_55,A_56)
      | v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_176,plain,(
    ! [C_15,A_11] :
      ( m1_subset_1(C_15,k1_zfmisc_1(A_11))
      | v1_xboole_0(k1_zfmisc_1(A_11))
      | ~ r1_tarski(C_15,A_11) ) ),
    inference(resolution,[status(thm)],[c_14,c_170])).

tff(c_180,plain,(
    ! [C_15,A_11] :
      ( m1_subset_1(C_15,k1_zfmisc_1(A_11))
      | ~ r1_tarski(C_15,A_11) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_176])).

tff(c_355,plain,(
    ! [A_83,B_84,C_85] :
      ( k4_subset_1(A_83,B_84,C_85) = k2_xboole_0(B_84,C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(A_83))
      | ~ m1_subset_1(B_84,k1_zfmisc_1(A_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_462,plain,(
    ! [A_92,B_93,C_94] :
      ( k4_subset_1(A_92,B_93,C_94) = k2_xboole_0(B_93,C_94)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(A_92))
      | ~ r1_tarski(C_94,A_92) ) ),
    inference(resolution,[status(thm)],[c_180,c_355])).

tff(c_476,plain,(
    ! [C_95] :
      ( k4_subset_1('#skF_3','#skF_4',C_95) = k2_xboole_0('#skF_4',C_95)
      | ~ r1_tarski(C_95,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_46,c_462])).

tff(c_573,plain,(
    ! [B_103] :
      ( k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3',B_103)) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3',B_103))
      | ~ m1_subset_1(B_103,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_233,c_476])).

tff(c_592,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_46,c_573])).

tff(c_600,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_592])).

tff(c_602,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_600])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n010.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 19:16:29 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.40/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.46  
% 2.56/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.46  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.56/1.46  
% 2.56/1.46  %Foreground sorts:
% 2.56/1.46  
% 2.56/1.46  
% 2.56/1.46  %Background operators:
% 2.56/1.46  
% 2.56/1.46  
% 2.56/1.46  %Foreground operators:
% 2.56/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.56/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.56/1.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.56/1.46  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.56/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.56/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.56/1.46  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.56/1.46  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.56/1.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.56/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.56/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.56/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.56/1.46  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.56/1.46  tff('#skF_4', type, '#skF_4': $i).
% 2.56/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.56/1.46  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.56/1.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.56/1.46  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.56/1.46  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.56/1.46  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.56/1.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.56/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.56/1.46  
% 2.56/1.48  tff(f_61, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.56/1.48  tff(f_83, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 2.56/1.48  tff(f_72, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.56/1.48  tff(f_59, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.56/1.48  tff(f_44, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.56/1.48  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.56/1.48  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.56/1.48  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.56/1.48  tff(f_69, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.56/1.48  tff(f_78, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.56/1.48  tff(c_34, plain, (![A_20]: (k2_subset_1(A_20)=A_20)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.56/1.48  tff(c_44, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.56/1.48  tff(c_47, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_44])).
% 2.56/1.48  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.56/1.48  tff(c_40, plain, (![A_25]: (~v1_xboole_0(k1_zfmisc_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.56/1.48  tff(c_135, plain, (![B_49, A_50]: (r2_hidden(B_49, A_50) | ~m1_subset_1(B_49, A_50) | v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.56/1.48  tff(c_12, plain, (![C_15, A_11]: (r1_tarski(C_15, A_11) | ~r2_hidden(C_15, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.56/1.48  tff(c_139, plain, (![B_49, A_11]: (r1_tarski(B_49, A_11) | ~m1_subset_1(B_49, k1_zfmisc_1(A_11)) | v1_xboole_0(k1_zfmisc_1(A_11)))), inference(resolution, [status(thm)], [c_135, c_12])).
% 2.56/1.48  tff(c_143, plain, (![B_51, A_52]: (r1_tarski(B_51, A_52) | ~m1_subset_1(B_51, k1_zfmisc_1(A_52)))), inference(negUnitSimplification, [status(thm)], [c_40, c_139])).
% 2.56/1.48  tff(c_152, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_143])).
% 2.56/1.48  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, B_6)=B_6 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.56/1.48  tff(c_165, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_152, c_6])).
% 2.56/1.48  tff(c_181, plain, (![A_57, B_58]: (k4_xboole_0(A_57, B_58)=k3_subset_1(A_57, B_58) | ~m1_subset_1(B_58, k1_zfmisc_1(A_57)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.56/1.48  tff(c_190, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_181])).
% 2.56/1.48  tff(c_8, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k4_xboole_0(B_8, A_7))=k2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.56/1.48  tff(c_194, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_190, c_8])).
% 2.56/1.48  tff(c_197, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_165, c_194])).
% 2.56/1.48  tff(c_222, plain, (![A_63, B_64]: (m1_subset_1(k3_subset_1(A_63, B_64), k1_zfmisc_1(A_63)) | ~m1_subset_1(B_64, k1_zfmisc_1(A_63)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.56/1.48  tff(c_142, plain, (![B_49, A_11]: (r1_tarski(B_49, A_11) | ~m1_subset_1(B_49, k1_zfmisc_1(A_11)))), inference(negUnitSimplification, [status(thm)], [c_40, c_139])).
% 2.56/1.48  tff(c_233, plain, (![A_63, B_64]: (r1_tarski(k3_subset_1(A_63, B_64), A_63) | ~m1_subset_1(B_64, k1_zfmisc_1(A_63)))), inference(resolution, [status(thm)], [c_222, c_142])).
% 2.56/1.48  tff(c_14, plain, (![C_15, A_11]: (r2_hidden(C_15, k1_zfmisc_1(A_11)) | ~r1_tarski(C_15, A_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.56/1.48  tff(c_170, plain, (![B_55, A_56]: (m1_subset_1(B_55, A_56) | ~r2_hidden(B_55, A_56) | v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.56/1.48  tff(c_176, plain, (![C_15, A_11]: (m1_subset_1(C_15, k1_zfmisc_1(A_11)) | v1_xboole_0(k1_zfmisc_1(A_11)) | ~r1_tarski(C_15, A_11))), inference(resolution, [status(thm)], [c_14, c_170])).
% 2.56/1.48  tff(c_180, plain, (![C_15, A_11]: (m1_subset_1(C_15, k1_zfmisc_1(A_11)) | ~r1_tarski(C_15, A_11))), inference(negUnitSimplification, [status(thm)], [c_40, c_176])).
% 2.56/1.48  tff(c_355, plain, (![A_83, B_84, C_85]: (k4_subset_1(A_83, B_84, C_85)=k2_xboole_0(B_84, C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(A_83)) | ~m1_subset_1(B_84, k1_zfmisc_1(A_83)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.56/1.48  tff(c_462, plain, (![A_92, B_93, C_94]: (k4_subset_1(A_92, B_93, C_94)=k2_xboole_0(B_93, C_94) | ~m1_subset_1(B_93, k1_zfmisc_1(A_92)) | ~r1_tarski(C_94, A_92))), inference(resolution, [status(thm)], [c_180, c_355])).
% 2.56/1.48  tff(c_476, plain, (![C_95]: (k4_subset_1('#skF_3', '#skF_4', C_95)=k2_xboole_0('#skF_4', C_95) | ~r1_tarski(C_95, '#skF_3'))), inference(resolution, [status(thm)], [c_46, c_462])).
% 2.56/1.48  tff(c_573, plain, (![B_103]: (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', B_103))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', B_103)) | ~m1_subset_1(B_103, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_233, c_476])).
% 2.56/1.48  tff(c_592, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_46, c_573])).
% 2.56/1.48  tff(c_600, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_197, c_592])).
% 2.56/1.48  tff(c_602, plain, $false, inference(negUnitSimplification, [status(thm)], [c_47, c_600])).
% 2.56/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.48  
% 2.56/1.48  Inference rules
% 2.56/1.48  ----------------------
% 2.56/1.48  #Ref     : 0
% 2.56/1.48  #Sup     : 124
% 2.56/1.48  #Fact    : 0
% 2.56/1.48  #Define  : 0
% 2.56/1.48  #Split   : 0
% 2.56/1.48  #Chain   : 0
% 2.56/1.48  #Close   : 0
% 2.56/1.48  
% 2.56/1.48  Ordering : KBO
% 2.56/1.48  
% 2.56/1.48  Simplification rules
% 2.56/1.48  ----------------------
% 2.56/1.48  #Subsume      : 15
% 2.56/1.48  #Demod        : 20
% 2.56/1.48  #Tautology    : 52
% 2.56/1.48  #SimpNegUnit  : 11
% 2.56/1.48  #BackRed      : 0
% 2.56/1.48  
% 2.56/1.48  #Partial instantiations: 0
% 2.56/1.48  #Strategies tried      : 1
% 2.56/1.48  
% 2.56/1.48  Timing (in seconds)
% 2.56/1.48  ----------------------
% 2.56/1.48  Preprocessing        : 0.31
% 2.56/1.48  Parsing              : 0.14
% 2.56/1.48  CNF conversion       : 0.02
% 2.56/1.48  Main loop            : 0.29
% 2.56/1.48  Inferencing          : 0.11
% 2.56/1.48  Reduction            : 0.09
% 2.56/1.48  Demodulation         : 0.06
% 2.56/1.48  BG Simplification    : 0.02
% 2.56/1.48  Subsumption          : 0.05
% 2.56/1.48  Abstraction          : 0.02
% 2.56/1.48  MUC search           : 0.00
% 2.56/1.48  Cooper               : 0.00
% 2.56/1.48  Total                : 0.62
% 2.56/1.48  Index Insertion      : 0.00
% 2.56/1.48  Index Deletion       : 0.00
% 2.56/1.48  Index Matching       : 0.00
% 2.56/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
