%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:28 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :   60 (  78 expanded)
%              Number of leaves         :   29 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :   77 ( 118 expanded)
%              Number of equality atoms :   23 (  29 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(f_57,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_79,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_68,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_55,axiom,(
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

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

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

tff(c_176,plain,(
    ! [B_45,A_46] :
      ( r2_hidden(B_45,A_46)
      | ~ m1_subset_1(B_45,A_46)
      | v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_8,plain,(
    ! [C_11,A_7] :
      ( r1_tarski(C_11,A_7)
      | ~ r2_hidden(C_11,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_180,plain,(
    ! [B_45,A_7] :
      ( r1_tarski(B_45,A_7)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_7))
      | v1_xboole_0(k1_zfmisc_1(A_7)) ) ),
    inference(resolution,[status(thm)],[c_176,c_8])).

tff(c_184,plain,(
    ! [B_47,A_48] :
      ( r1_tarski(B_47,A_48)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_48)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_180])).

tff(c_193,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_184])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k2_xboole_0(A_1,B_2) = B_2
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_197,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_193,c_2])).

tff(c_246,plain,(
    ! [A_59,B_60] :
      ( k4_xboole_0(A_59,B_60) = k3_subset_1(A_59,B_60)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_263,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_246])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_277,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_4])).

tff(c_280,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_277])).

tff(c_231,plain,(
    ! [A_55,B_56] :
      ( m1_subset_1(k3_subset_1(A_55,B_56),k1_zfmisc_1(A_55))
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_183,plain,(
    ! [B_45,A_7] :
      ( r1_tarski(B_45,A_7)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_7)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_180])).

tff(c_238,plain,(
    ! [A_55,B_56] :
      ( r1_tarski(k3_subset_1(A_55,B_56),A_55)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_55)) ) ),
    inference(resolution,[status(thm)],[c_231,c_183])).

tff(c_10,plain,(
    ! [C_11,A_7] :
      ( r2_hidden(C_11,k1_zfmisc_1(A_7))
      | ~ r1_tarski(C_11,A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_211,plain,(
    ! [B_51,A_52] :
      ( m1_subset_1(B_51,A_52)
      | ~ r2_hidden(B_51,A_52)
      | v1_xboole_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_217,plain,(
    ! [C_11,A_7] :
      ( m1_subset_1(C_11,k1_zfmisc_1(A_7))
      | v1_xboole_0(k1_zfmisc_1(A_7))
      | ~ r1_tarski(C_11,A_7) ) ),
    inference(resolution,[status(thm)],[c_10,c_211])).

tff(c_221,plain,(
    ! [C_11,A_7] :
      ( m1_subset_1(C_11,k1_zfmisc_1(A_7))
      | ~ r1_tarski(C_11,A_7) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_217])).

tff(c_408,plain,(
    ! [A_79,B_80,C_81] :
      ( k4_subset_1(A_79,B_80,C_81) = k2_xboole_0(B_80,C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(A_79))
      | ~ m1_subset_1(B_80,k1_zfmisc_1(A_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_562,plain,(
    ! [A_90,B_91,C_92] :
      ( k4_subset_1(A_90,B_91,C_92) = k2_xboole_0(B_91,C_92)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(A_90))
      | ~ r1_tarski(C_92,A_90) ) ),
    inference(resolution,[status(thm)],[c_221,c_408])).

tff(c_582,plain,(
    ! [C_93] :
      ( k4_subset_1('#skF_3','#skF_4',C_93) = k2_xboole_0('#skF_4',C_93)
      | ~ r1_tarski(C_93,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_42,c_562])).

tff(c_613,plain,(
    ! [B_97] :
      ( k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3',B_97)) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3',B_97))
      | ~ m1_subset_1(B_97,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_238,c_582])).

tff(c_632,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_42,c_613])).

tff(c_640,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_632])).

tff(c_642,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_640])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.10/0.31  % Computer   : n011.cluster.edu
% 0.10/0.31  % Model      : x86_64 x86_64
% 0.10/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.31  % Memory     : 8042.1875MB
% 0.10/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.31  % CPULimit   : 60
% 0.10/0.31  % DateTime   : Tue Dec  1 16:30:27 EST 2020
% 0.10/0.31  % CPUTime    : 
% 0.16/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.65/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.34  
% 2.65/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.35  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.65/1.35  
% 2.65/1.35  %Foreground sorts:
% 2.65/1.35  
% 2.65/1.35  
% 2.65/1.35  %Background operators:
% 2.65/1.35  
% 2.65/1.35  
% 2.65/1.35  %Foreground operators:
% 2.65/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.65/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.65/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.65/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.65/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.65/1.35  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.65/1.35  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.65/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.65/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.65/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.65/1.35  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.65/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.65/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.65/1.35  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.65/1.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.65/1.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.65/1.35  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.65/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.65/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.65/1.35  
% 2.65/1.36  tff(f_57, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.65/1.36  tff(f_79, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 2.65/1.36  tff(f_68, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.65/1.36  tff(f_55, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.65/1.36  tff(f_40, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.65/1.36  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.65/1.36  tff(f_61, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.65/1.36  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.65/1.36  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.65/1.36  tff(f_74, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.65/1.36  tff(c_30, plain, (![A_16]: (k2_subset_1(A_16)=A_16)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.65/1.36  tff(c_40, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.65/1.36  tff(c_43, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_40])).
% 2.65/1.36  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.65/1.36  tff(c_36, plain, (![A_21]: (~v1_xboole_0(k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.65/1.36  tff(c_176, plain, (![B_45, A_46]: (r2_hidden(B_45, A_46) | ~m1_subset_1(B_45, A_46) | v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.65/1.36  tff(c_8, plain, (![C_11, A_7]: (r1_tarski(C_11, A_7) | ~r2_hidden(C_11, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.65/1.36  tff(c_180, plain, (![B_45, A_7]: (r1_tarski(B_45, A_7) | ~m1_subset_1(B_45, k1_zfmisc_1(A_7)) | v1_xboole_0(k1_zfmisc_1(A_7)))), inference(resolution, [status(thm)], [c_176, c_8])).
% 2.65/1.36  tff(c_184, plain, (![B_47, A_48]: (r1_tarski(B_47, A_48) | ~m1_subset_1(B_47, k1_zfmisc_1(A_48)))), inference(negUnitSimplification, [status(thm)], [c_36, c_180])).
% 2.65/1.36  tff(c_193, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_184])).
% 2.65/1.36  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(A_1, B_2)=B_2 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.65/1.36  tff(c_197, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_193, c_2])).
% 2.65/1.36  tff(c_246, plain, (![A_59, B_60]: (k4_xboole_0(A_59, B_60)=k3_subset_1(A_59, B_60) | ~m1_subset_1(B_60, k1_zfmisc_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.65/1.36  tff(c_263, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_246])).
% 2.65/1.36  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.65/1.36  tff(c_277, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_263, c_4])).
% 2.65/1.36  tff(c_280, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_197, c_277])).
% 2.65/1.36  tff(c_231, plain, (![A_55, B_56]: (m1_subset_1(k3_subset_1(A_55, B_56), k1_zfmisc_1(A_55)) | ~m1_subset_1(B_56, k1_zfmisc_1(A_55)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.65/1.36  tff(c_183, plain, (![B_45, A_7]: (r1_tarski(B_45, A_7) | ~m1_subset_1(B_45, k1_zfmisc_1(A_7)))), inference(negUnitSimplification, [status(thm)], [c_36, c_180])).
% 2.65/1.36  tff(c_238, plain, (![A_55, B_56]: (r1_tarski(k3_subset_1(A_55, B_56), A_55) | ~m1_subset_1(B_56, k1_zfmisc_1(A_55)))), inference(resolution, [status(thm)], [c_231, c_183])).
% 2.65/1.36  tff(c_10, plain, (![C_11, A_7]: (r2_hidden(C_11, k1_zfmisc_1(A_7)) | ~r1_tarski(C_11, A_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.65/1.36  tff(c_211, plain, (![B_51, A_52]: (m1_subset_1(B_51, A_52) | ~r2_hidden(B_51, A_52) | v1_xboole_0(A_52))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.65/1.36  tff(c_217, plain, (![C_11, A_7]: (m1_subset_1(C_11, k1_zfmisc_1(A_7)) | v1_xboole_0(k1_zfmisc_1(A_7)) | ~r1_tarski(C_11, A_7))), inference(resolution, [status(thm)], [c_10, c_211])).
% 2.65/1.36  tff(c_221, plain, (![C_11, A_7]: (m1_subset_1(C_11, k1_zfmisc_1(A_7)) | ~r1_tarski(C_11, A_7))), inference(negUnitSimplification, [status(thm)], [c_36, c_217])).
% 2.65/1.36  tff(c_408, plain, (![A_79, B_80, C_81]: (k4_subset_1(A_79, B_80, C_81)=k2_xboole_0(B_80, C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(A_79)) | ~m1_subset_1(B_80, k1_zfmisc_1(A_79)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.65/1.36  tff(c_562, plain, (![A_90, B_91, C_92]: (k4_subset_1(A_90, B_91, C_92)=k2_xboole_0(B_91, C_92) | ~m1_subset_1(B_91, k1_zfmisc_1(A_90)) | ~r1_tarski(C_92, A_90))), inference(resolution, [status(thm)], [c_221, c_408])).
% 2.65/1.36  tff(c_582, plain, (![C_93]: (k4_subset_1('#skF_3', '#skF_4', C_93)=k2_xboole_0('#skF_4', C_93) | ~r1_tarski(C_93, '#skF_3'))), inference(resolution, [status(thm)], [c_42, c_562])).
% 2.65/1.36  tff(c_613, plain, (![B_97]: (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', B_97))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', B_97)) | ~m1_subset_1(B_97, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_238, c_582])).
% 2.65/1.36  tff(c_632, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_42, c_613])).
% 2.65/1.36  tff(c_640, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_280, c_632])).
% 2.65/1.36  tff(c_642, plain, $false, inference(negUnitSimplification, [status(thm)], [c_43, c_640])).
% 2.65/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.36  
% 2.65/1.36  Inference rules
% 2.65/1.36  ----------------------
% 2.65/1.36  #Ref     : 0
% 2.65/1.36  #Sup     : 136
% 2.65/1.36  #Fact    : 0
% 2.65/1.36  #Define  : 0
% 2.65/1.36  #Split   : 0
% 2.65/1.36  #Chain   : 0
% 2.65/1.36  #Close   : 0
% 2.65/1.36  
% 2.65/1.36  Ordering : KBO
% 2.65/1.36  
% 2.65/1.36  Simplification rules
% 2.65/1.36  ----------------------
% 2.65/1.36  #Subsume      : 15
% 2.65/1.36  #Demod        : 23
% 2.65/1.36  #Tautology    : 61
% 2.65/1.36  #SimpNegUnit  : 11
% 2.65/1.36  #BackRed      : 0
% 2.65/1.36  
% 2.65/1.36  #Partial instantiations: 0
% 2.65/1.36  #Strategies tried      : 1
% 2.65/1.36  
% 2.65/1.36  Timing (in seconds)
% 2.65/1.36  ----------------------
% 2.65/1.36  Preprocessing        : 0.31
% 2.65/1.36  Parsing              : 0.17
% 2.65/1.36  CNF conversion       : 0.02
% 2.65/1.36  Main loop            : 0.32
% 2.65/1.36  Inferencing          : 0.13
% 2.65/1.36  Reduction            : 0.10
% 2.65/1.36  Demodulation         : 0.07
% 2.65/1.36  BG Simplification    : 0.02
% 2.65/1.36  Subsumption          : 0.06
% 2.65/1.36  Abstraction          : 0.02
% 2.65/1.36  MUC search           : 0.00
% 2.65/1.36  Cooper               : 0.00
% 2.65/1.36  Total                : 0.66
% 2.65/1.36  Index Insertion      : 0.00
% 2.65/1.36  Index Deletion       : 0.00
% 2.65/1.36  Index Matching       : 0.00
% 2.65/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
