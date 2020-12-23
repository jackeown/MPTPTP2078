%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:36 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :   57 (  75 expanded)
%              Number of leaves         :   28 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :   75 ( 116 expanded)
%              Number of equality atoms :   20 (  26 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

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

tff(f_53,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_77,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_64,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_26,plain,(
    ! [A_11] : k2_subset_1(A_11) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_38,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_42,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_38])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_32,plain,(
    ! [A_16] : ~ v1_xboole_0(k1_zfmisc_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_98,plain,(
    ! [B_37,A_38] :
      ( r2_hidden(B_37,A_38)
      | ~ m1_subset_1(B_37,A_38)
      | v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4,plain,(
    ! [C_7,A_3] :
      ( r1_tarski(C_7,A_3)
      | ~ r2_hidden(C_7,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_105,plain,(
    ! [B_37,A_3] :
      ( r1_tarski(B_37,A_3)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_3))
      | v1_xboole_0(k1_zfmisc_1(A_3)) ) ),
    inference(resolution,[status(thm)],[c_98,c_4])).

tff(c_110,plain,(
    ! [B_39,A_40] :
      ( r1_tarski(B_39,A_40)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_40)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_105])).

tff(c_123,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_110])).

tff(c_167,plain,(
    ! [A_47,B_48] :
      ( k4_xboole_0(A_47,B_48) = k3_subset_1(A_47,B_48)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_188,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_167])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k2_xboole_0(A_1,k4_xboole_0(B_2,A_1)) = B_2
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_192,plain,
    ( k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_2])).

tff(c_196,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_192])).

tff(c_133,plain,(
    ! [A_43,B_44] :
      ( m1_subset_1(k3_subset_1(A_43,B_44),k1_zfmisc_1(A_43))
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_109,plain,(
    ! [B_37,A_3] :
      ( r1_tarski(B_37,A_3)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_3)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_105])).

tff(c_143,plain,(
    ! [A_43,B_44] :
      ( r1_tarski(k3_subset_1(A_43,B_44),A_43)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_43)) ) ),
    inference(resolution,[status(thm)],[c_133,c_109])).

tff(c_6,plain,(
    ! [C_7,A_3] :
      ( r2_hidden(C_7,k1_zfmisc_1(A_3))
      | ~ r1_tarski(C_7,A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_86,plain,(
    ! [B_33,A_34] :
      ( m1_subset_1(B_33,A_34)
      | ~ r2_hidden(B_33,A_34)
      | v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_89,plain,(
    ! [C_7,A_3] :
      ( m1_subset_1(C_7,k1_zfmisc_1(A_3))
      | v1_xboole_0(k1_zfmisc_1(A_3))
      | ~ r1_tarski(C_7,A_3) ) ),
    inference(resolution,[status(thm)],[c_6,c_86])).

tff(c_92,plain,(
    ! [C_7,A_3] :
      ( m1_subset_1(C_7,k1_zfmisc_1(A_3))
      | ~ r1_tarski(C_7,A_3) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_89])).

tff(c_343,plain,(
    ! [A_69,B_70,C_71] :
      ( k4_subset_1(A_69,B_70,C_71) = k2_xboole_0(B_70,C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(A_69))
      | ~ m1_subset_1(B_70,k1_zfmisc_1(A_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_404,plain,(
    ! [A_74,B_75,C_76] :
      ( k4_subset_1(A_74,B_75,C_76) = k2_xboole_0(B_75,C_76)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_74))
      | ~ r1_tarski(C_76,A_74) ) ),
    inference(resolution,[status(thm)],[c_92,c_343])).

tff(c_421,plain,(
    ! [C_77] :
      ( k4_subset_1('#skF_3','#skF_4',C_77) = k2_xboole_0('#skF_4',C_77)
      | ~ r1_tarski(C_77,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_40,c_404])).

tff(c_677,plain,(
    ! [B_98] :
      ( k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3',B_98)) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3',B_98))
      | ~ m1_subset_1(B_98,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_143,c_421])).

tff(c_704,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_40,c_677])).

tff(c_716,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_704])).

tff(c_718,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_716])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:51:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.70/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.45  
% 2.70/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.46  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.70/1.46  
% 2.70/1.46  %Foreground sorts:
% 2.70/1.46  
% 2.70/1.46  
% 2.70/1.46  %Background operators:
% 2.70/1.46  
% 2.70/1.46  
% 2.70/1.46  %Foreground operators:
% 2.70/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.70/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.70/1.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.70/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.70/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.70/1.46  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.70/1.46  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.70/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.70/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.70/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.70/1.46  tff('#skF_4', type, '#skF_4': $i).
% 2.70/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.70/1.46  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.70/1.46  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.70/1.46  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.70/1.46  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.70/1.46  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.70/1.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.70/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.70/1.46  
% 2.70/1.47  tff(f_53, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.70/1.47  tff(f_77, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 2.70/1.47  tff(f_64, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.70/1.47  tff(f_49, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.70/1.47  tff(f_36, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.70/1.47  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.70/1.47  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_xboole_1)).
% 2.70/1.47  tff(f_61, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.70/1.47  tff(f_70, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.70/1.47  tff(c_26, plain, (![A_11]: (k2_subset_1(A_11)=A_11)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.70/1.47  tff(c_38, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.70/1.47  tff(c_42, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_38])).
% 2.70/1.47  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.70/1.47  tff(c_32, plain, (![A_16]: (~v1_xboole_0(k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.70/1.47  tff(c_98, plain, (![B_37, A_38]: (r2_hidden(B_37, A_38) | ~m1_subset_1(B_37, A_38) | v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.70/1.47  tff(c_4, plain, (![C_7, A_3]: (r1_tarski(C_7, A_3) | ~r2_hidden(C_7, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.70/1.47  tff(c_105, plain, (![B_37, A_3]: (r1_tarski(B_37, A_3) | ~m1_subset_1(B_37, k1_zfmisc_1(A_3)) | v1_xboole_0(k1_zfmisc_1(A_3)))), inference(resolution, [status(thm)], [c_98, c_4])).
% 2.70/1.47  tff(c_110, plain, (![B_39, A_40]: (r1_tarski(B_39, A_40) | ~m1_subset_1(B_39, k1_zfmisc_1(A_40)))), inference(negUnitSimplification, [status(thm)], [c_32, c_105])).
% 2.70/1.47  tff(c_123, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_110])).
% 2.70/1.47  tff(c_167, plain, (![A_47, B_48]: (k4_xboole_0(A_47, B_48)=k3_subset_1(A_47, B_48) | ~m1_subset_1(B_48, k1_zfmisc_1(A_47)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.70/1.47  tff(c_188, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_167])).
% 2.70/1.47  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k4_xboole_0(B_2, A_1))=B_2 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.70/1.47  tff(c_192, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3' | ~r1_tarski('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_188, c_2])).
% 2.70/1.47  tff(c_196, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_123, c_192])).
% 2.70/1.47  tff(c_133, plain, (![A_43, B_44]: (m1_subset_1(k3_subset_1(A_43, B_44), k1_zfmisc_1(A_43)) | ~m1_subset_1(B_44, k1_zfmisc_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.70/1.47  tff(c_109, plain, (![B_37, A_3]: (r1_tarski(B_37, A_3) | ~m1_subset_1(B_37, k1_zfmisc_1(A_3)))), inference(negUnitSimplification, [status(thm)], [c_32, c_105])).
% 2.70/1.47  tff(c_143, plain, (![A_43, B_44]: (r1_tarski(k3_subset_1(A_43, B_44), A_43) | ~m1_subset_1(B_44, k1_zfmisc_1(A_43)))), inference(resolution, [status(thm)], [c_133, c_109])).
% 2.70/1.47  tff(c_6, plain, (![C_7, A_3]: (r2_hidden(C_7, k1_zfmisc_1(A_3)) | ~r1_tarski(C_7, A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.70/1.47  tff(c_86, plain, (![B_33, A_34]: (m1_subset_1(B_33, A_34) | ~r2_hidden(B_33, A_34) | v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.70/1.47  tff(c_89, plain, (![C_7, A_3]: (m1_subset_1(C_7, k1_zfmisc_1(A_3)) | v1_xboole_0(k1_zfmisc_1(A_3)) | ~r1_tarski(C_7, A_3))), inference(resolution, [status(thm)], [c_6, c_86])).
% 2.70/1.47  tff(c_92, plain, (![C_7, A_3]: (m1_subset_1(C_7, k1_zfmisc_1(A_3)) | ~r1_tarski(C_7, A_3))), inference(negUnitSimplification, [status(thm)], [c_32, c_89])).
% 2.70/1.47  tff(c_343, plain, (![A_69, B_70, C_71]: (k4_subset_1(A_69, B_70, C_71)=k2_xboole_0(B_70, C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(A_69)) | ~m1_subset_1(B_70, k1_zfmisc_1(A_69)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.70/1.47  tff(c_404, plain, (![A_74, B_75, C_76]: (k4_subset_1(A_74, B_75, C_76)=k2_xboole_0(B_75, C_76) | ~m1_subset_1(B_75, k1_zfmisc_1(A_74)) | ~r1_tarski(C_76, A_74))), inference(resolution, [status(thm)], [c_92, c_343])).
% 2.70/1.47  tff(c_421, plain, (![C_77]: (k4_subset_1('#skF_3', '#skF_4', C_77)=k2_xboole_0('#skF_4', C_77) | ~r1_tarski(C_77, '#skF_3'))), inference(resolution, [status(thm)], [c_40, c_404])).
% 2.70/1.47  tff(c_677, plain, (![B_98]: (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', B_98))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', B_98)) | ~m1_subset_1(B_98, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_143, c_421])).
% 2.70/1.47  tff(c_704, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_40, c_677])).
% 2.70/1.47  tff(c_716, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_196, c_704])).
% 2.70/1.47  tff(c_718, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_716])).
% 2.70/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.47  
% 2.70/1.47  Inference rules
% 2.70/1.47  ----------------------
% 2.70/1.47  #Ref     : 0
% 2.70/1.47  #Sup     : 145
% 2.70/1.47  #Fact    : 0
% 2.70/1.47  #Define  : 0
% 2.70/1.47  #Split   : 3
% 2.70/1.47  #Chain   : 0
% 2.70/1.47  #Close   : 0
% 2.70/1.47  
% 2.70/1.47  Ordering : KBO
% 2.70/1.47  
% 2.70/1.47  Simplification rules
% 2.70/1.47  ----------------------
% 2.70/1.47  #Subsume      : 26
% 2.70/1.47  #Demod        : 16
% 2.70/1.47  #Tautology    : 39
% 2.70/1.47  #SimpNegUnit  : 22
% 2.70/1.47  #BackRed      : 0
% 2.70/1.47  
% 2.70/1.47  #Partial instantiations: 0
% 2.70/1.47  #Strategies tried      : 1
% 2.70/1.47  
% 2.70/1.47  Timing (in seconds)
% 2.70/1.47  ----------------------
% 2.70/1.47  Preprocessing        : 0.29
% 2.70/1.47  Parsing              : 0.15
% 2.70/1.47  CNF conversion       : 0.02
% 2.70/1.47  Main loop            : 0.32
% 2.70/1.47  Inferencing          : 0.12
% 2.70/1.47  Reduction            : 0.09
% 2.70/1.47  Demodulation         : 0.06
% 2.70/1.47  BG Simplification    : 0.02
% 2.70/1.47  Subsumption          : 0.07
% 2.70/1.47  Abstraction          : 0.02
% 2.70/1.47  MUC search           : 0.00
% 2.70/1.47  Cooper               : 0.00
% 2.70/1.47  Total                : 0.64
% 2.70/1.47  Index Insertion      : 0.00
% 2.70/1.47  Index Deletion       : 0.00
% 2.70/1.47  Index Matching       : 0.00
% 2.70/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
