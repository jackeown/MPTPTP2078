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
% DateTime   : Thu Dec  3 09:55:36 EST 2020

% Result     : Theorem 2.56s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :   59 (  77 expanded)
%              Number of leaves         :   28 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :   77 ( 118 expanded)
%              Number of equality atoms :   23 (  29 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

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

tff(f_55,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_77,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_66,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_28,plain,(
    ! [A_14] : k2_subset_1(A_14) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_38,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_41,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_38])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_34,plain,(
    ! [A_19] : ~ v1_xboole_0(k1_zfmisc_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_78,plain,(
    ! [B_37,A_38] :
      ( r2_hidden(B_37,A_38)
      | ~ m1_subset_1(B_37,A_38)
      | v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_8,plain,(
    ! [C_11,A_7] :
      ( r1_tarski(C_11,A_7)
      | ~ r2_hidden(C_11,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_82,plain,(
    ! [B_37,A_7] :
      ( r1_tarski(B_37,A_7)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_7))
      | v1_xboole_0(k1_zfmisc_1(A_7)) ) ),
    inference(resolution,[status(thm)],[c_78,c_8])).

tff(c_86,plain,(
    ! [B_39,A_40] :
      ( r1_tarski(B_39,A_40)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_40)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_82])).

tff(c_95,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_86])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k2_xboole_0(A_1,B_2) = B_2
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_99,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_95,c_2])).

tff(c_133,plain,(
    ! [A_47,B_48] :
      ( k4_xboole_0(A_47,B_48) = k3_subset_1(A_47,B_48)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_146,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_133])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_153,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_4])).

tff(c_157,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_153])).

tff(c_173,plain,(
    ! [A_51,B_52] :
      ( m1_subset_1(k3_subset_1(A_51,B_52),k1_zfmisc_1(A_51))
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_85,plain,(
    ! [B_37,A_7] :
      ( r1_tarski(B_37,A_7)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_7)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_82])).

tff(c_184,plain,(
    ! [A_51,B_52] :
      ( r1_tarski(k3_subset_1(A_51,B_52),A_51)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_51)) ) ),
    inference(resolution,[status(thm)],[c_173,c_85])).

tff(c_10,plain,(
    ! [C_11,A_7] :
      ( r2_hidden(C_11,k1_zfmisc_1(A_7))
      | ~ r1_tarski(C_11,A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_113,plain,(
    ! [B_43,A_44] :
      ( m1_subset_1(B_43,A_44)
      | ~ r2_hidden(B_43,A_44)
      | v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_119,plain,(
    ! [C_11,A_7] :
      ( m1_subset_1(C_11,k1_zfmisc_1(A_7))
      | v1_xboole_0(k1_zfmisc_1(A_7))
      | ~ r1_tarski(C_11,A_7) ) ),
    inference(resolution,[status(thm)],[c_10,c_113])).

tff(c_123,plain,(
    ! [C_11,A_7] :
      ( m1_subset_1(C_11,k1_zfmisc_1(A_7))
      | ~ r1_tarski(C_11,A_7) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_119])).

tff(c_335,plain,(
    ! [A_73,B_74,C_75] :
      ( k4_subset_1(A_73,B_74,C_75) = k2_xboole_0(B_74,C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(A_73))
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_421,plain,(
    ! [A_80,B_81,C_82] :
      ( k4_subset_1(A_80,B_81,C_82) = k2_xboole_0(B_81,C_82)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(A_80))
      | ~ r1_tarski(C_82,A_80) ) ),
    inference(resolution,[status(thm)],[c_123,c_335])).

tff(c_435,plain,(
    ! [C_83] :
      ( k4_subset_1('#skF_3','#skF_4',C_83) = k2_xboole_0('#skF_4',C_83)
      | ~ r1_tarski(C_83,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_40,c_421])).

tff(c_652,plain,(
    ! [B_97] :
      ( k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3',B_97)) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3',B_97))
      | ~ m1_subset_1(B_97,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_184,c_435])).

tff(c_675,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_40,c_652])).

tff(c_686,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_675])).

tff(c_688,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_41,c_686])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:25:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.56/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.37  
% 2.56/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.37  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.56/1.37  
% 2.56/1.37  %Foreground sorts:
% 2.56/1.37  
% 2.56/1.37  
% 2.56/1.37  %Background operators:
% 2.56/1.37  
% 2.56/1.37  
% 2.56/1.37  %Foreground operators:
% 2.56/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.56/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.56/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.56/1.37  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.56/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.56/1.37  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.56/1.37  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.56/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.56/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.56/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.56/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.56/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.56/1.37  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.56/1.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.56/1.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.56/1.37  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.56/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.56/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.56/1.37  
% 2.56/1.38  tff(f_55, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.56/1.38  tff(f_77, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 2.56/1.38  tff(f_66, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.56/1.38  tff(f_53, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.56/1.38  tff(f_40, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.56/1.38  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.56/1.38  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.56/1.38  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.56/1.38  tff(f_63, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.56/1.38  tff(f_72, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.56/1.38  tff(c_28, plain, (![A_14]: (k2_subset_1(A_14)=A_14)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.56/1.38  tff(c_38, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.56/1.38  tff(c_41, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_38])).
% 2.56/1.38  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.56/1.38  tff(c_34, plain, (![A_19]: (~v1_xboole_0(k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.56/1.38  tff(c_78, plain, (![B_37, A_38]: (r2_hidden(B_37, A_38) | ~m1_subset_1(B_37, A_38) | v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.56/1.38  tff(c_8, plain, (![C_11, A_7]: (r1_tarski(C_11, A_7) | ~r2_hidden(C_11, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.56/1.38  tff(c_82, plain, (![B_37, A_7]: (r1_tarski(B_37, A_7) | ~m1_subset_1(B_37, k1_zfmisc_1(A_7)) | v1_xboole_0(k1_zfmisc_1(A_7)))), inference(resolution, [status(thm)], [c_78, c_8])).
% 2.56/1.38  tff(c_86, plain, (![B_39, A_40]: (r1_tarski(B_39, A_40) | ~m1_subset_1(B_39, k1_zfmisc_1(A_40)))), inference(negUnitSimplification, [status(thm)], [c_34, c_82])).
% 2.56/1.38  tff(c_95, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_86])).
% 2.56/1.38  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(A_1, B_2)=B_2 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.56/1.38  tff(c_99, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_95, c_2])).
% 2.56/1.38  tff(c_133, plain, (![A_47, B_48]: (k4_xboole_0(A_47, B_48)=k3_subset_1(A_47, B_48) | ~m1_subset_1(B_48, k1_zfmisc_1(A_47)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.56/1.38  tff(c_146, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_133])).
% 2.56/1.38  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.56/1.38  tff(c_153, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_146, c_4])).
% 2.56/1.38  tff(c_157, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_99, c_153])).
% 2.56/1.38  tff(c_173, plain, (![A_51, B_52]: (m1_subset_1(k3_subset_1(A_51, B_52), k1_zfmisc_1(A_51)) | ~m1_subset_1(B_52, k1_zfmisc_1(A_51)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.56/1.38  tff(c_85, plain, (![B_37, A_7]: (r1_tarski(B_37, A_7) | ~m1_subset_1(B_37, k1_zfmisc_1(A_7)))), inference(negUnitSimplification, [status(thm)], [c_34, c_82])).
% 2.56/1.38  tff(c_184, plain, (![A_51, B_52]: (r1_tarski(k3_subset_1(A_51, B_52), A_51) | ~m1_subset_1(B_52, k1_zfmisc_1(A_51)))), inference(resolution, [status(thm)], [c_173, c_85])).
% 2.56/1.38  tff(c_10, plain, (![C_11, A_7]: (r2_hidden(C_11, k1_zfmisc_1(A_7)) | ~r1_tarski(C_11, A_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.56/1.38  tff(c_113, plain, (![B_43, A_44]: (m1_subset_1(B_43, A_44) | ~r2_hidden(B_43, A_44) | v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.56/1.38  tff(c_119, plain, (![C_11, A_7]: (m1_subset_1(C_11, k1_zfmisc_1(A_7)) | v1_xboole_0(k1_zfmisc_1(A_7)) | ~r1_tarski(C_11, A_7))), inference(resolution, [status(thm)], [c_10, c_113])).
% 2.56/1.38  tff(c_123, plain, (![C_11, A_7]: (m1_subset_1(C_11, k1_zfmisc_1(A_7)) | ~r1_tarski(C_11, A_7))), inference(negUnitSimplification, [status(thm)], [c_34, c_119])).
% 2.56/1.38  tff(c_335, plain, (![A_73, B_74, C_75]: (k4_subset_1(A_73, B_74, C_75)=k2_xboole_0(B_74, C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(A_73)) | ~m1_subset_1(B_74, k1_zfmisc_1(A_73)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.56/1.38  tff(c_421, plain, (![A_80, B_81, C_82]: (k4_subset_1(A_80, B_81, C_82)=k2_xboole_0(B_81, C_82) | ~m1_subset_1(B_81, k1_zfmisc_1(A_80)) | ~r1_tarski(C_82, A_80))), inference(resolution, [status(thm)], [c_123, c_335])).
% 2.56/1.38  tff(c_435, plain, (![C_83]: (k4_subset_1('#skF_3', '#skF_4', C_83)=k2_xboole_0('#skF_4', C_83) | ~r1_tarski(C_83, '#skF_3'))), inference(resolution, [status(thm)], [c_40, c_421])).
% 2.56/1.38  tff(c_652, plain, (![B_97]: (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', B_97))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', B_97)) | ~m1_subset_1(B_97, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_184, c_435])).
% 2.56/1.38  tff(c_675, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_40, c_652])).
% 2.56/1.38  tff(c_686, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_157, c_675])).
% 2.56/1.38  tff(c_688, plain, $false, inference(negUnitSimplification, [status(thm)], [c_41, c_686])).
% 2.56/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.38  
% 2.56/1.38  Inference rules
% 2.56/1.38  ----------------------
% 2.56/1.38  #Ref     : 0
% 2.56/1.38  #Sup     : 142
% 2.56/1.38  #Fact    : 0
% 2.56/1.38  #Define  : 0
% 2.56/1.38  #Split   : 0
% 2.56/1.38  #Chain   : 0
% 2.56/1.38  #Close   : 0
% 2.56/1.38  
% 2.56/1.38  Ordering : KBO
% 2.83/1.38  
% 2.83/1.38  Simplification rules
% 2.83/1.38  ----------------------
% 2.83/1.38  #Subsume      : 15
% 2.83/1.38  #Demod        : 15
% 2.83/1.38  #Tautology    : 53
% 2.83/1.38  #SimpNegUnit  : 22
% 2.83/1.38  #BackRed      : 0
% 2.83/1.38  
% 2.83/1.38  #Partial instantiations: 0
% 2.83/1.38  #Strategies tried      : 1
% 2.83/1.38  
% 2.83/1.38  Timing (in seconds)
% 2.83/1.38  ----------------------
% 2.83/1.39  Preprocessing        : 0.30
% 2.83/1.39  Parsing              : 0.16
% 2.83/1.39  CNF conversion       : 0.02
% 2.83/1.39  Main loop            : 0.31
% 2.83/1.39  Inferencing          : 0.12
% 2.83/1.39  Reduction            : 0.09
% 2.83/1.39  Demodulation         : 0.06
% 2.83/1.39  BG Simplification    : 0.02
% 2.83/1.39  Subsumption          : 0.06
% 2.83/1.39  Abstraction          : 0.03
% 2.83/1.39  MUC search           : 0.00
% 2.83/1.39  Cooper               : 0.00
% 2.83/1.39  Total                : 0.65
% 2.83/1.39  Index Insertion      : 0.00
% 2.83/1.39  Index Deletion       : 0.00
% 2.83/1.39  Index Matching       : 0.00
% 2.83/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
