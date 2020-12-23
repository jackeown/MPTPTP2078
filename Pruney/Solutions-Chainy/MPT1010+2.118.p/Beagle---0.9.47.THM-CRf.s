%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:21 EST 2020

% Result     : Theorem 3.89s
% Output     : CNFRefutation 3.89s
% Verified   : 
% Statistics : Number of formulae       :   54 (  60 expanded)
%              Number of leaves         :   34 (  39 expanded)
%              Depth                    :    7
%              Number of atoms          :   61 (  87 expanded)
%              Number of equality atoms :   25 (  31 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_46,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(c_50,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_90,plain,(
    ! [A_55,B_56] :
      ( k4_xboole_0(A_55,B_56) = k1_xboole_0
      | ~ r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_94,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_90])).

tff(c_44,plain,(
    ! [B_40] : k4_xboole_0(k1_tarski(B_40),k1_tarski(B_40)) != k1_tarski(B_40) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_95,plain,(
    ! [B_40] : k1_tarski(B_40) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_44])).

tff(c_58,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_56,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_54,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_52,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2347,plain,(
    ! [D_7253,C_7254,B_7255,A_7256] :
      ( r2_hidden(k1_funct_1(D_7253,C_7254),B_7255)
      | k1_xboole_0 = B_7255
      | ~ r2_hidden(C_7254,A_7256)
      | ~ m1_subset_1(D_7253,k1_zfmisc_1(k2_zfmisc_1(A_7256,B_7255)))
      | ~ v1_funct_2(D_7253,A_7256,B_7255)
      | ~ v1_funct_1(D_7253) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2623,plain,(
    ! [D_7999,B_8000] :
      ( r2_hidden(k1_funct_1(D_7999,'#skF_5'),B_8000)
      | k1_xboole_0 = B_8000
      | ~ m1_subset_1(D_7999,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_8000)))
      | ~ v1_funct_2(D_7999,'#skF_3',B_8000)
      | ~ v1_funct_1(D_7999) ) ),
    inference(resolution,[status(thm)],[c_52,c_2347])).

tff(c_2632,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_2623])).

tff(c_2635,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_2632])).

tff(c_2636,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_2635])).

tff(c_30,plain,(
    ! [A_11] : k2_tarski(A_11,A_11) = k1_tarski(A_11) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_119,plain,(
    ! [D_63,B_64,A_65] :
      ( D_63 = B_64
      | D_63 = A_65
      | ~ r2_hidden(D_63,k2_tarski(A_65,B_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_125,plain,(
    ! [D_63,A_11] :
      ( D_63 = A_11
      | D_63 = A_11
      | ~ r2_hidden(D_63,k1_tarski(A_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_119])).

tff(c_2643,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2636,c_125])).

tff(c_2693,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_50,c_2643])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:00:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.89/1.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.89/1.65  
% 3.89/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.89/1.65  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 3.89/1.65  
% 3.89/1.65  %Foreground sorts:
% 3.89/1.65  
% 3.89/1.65  
% 3.89/1.65  %Background operators:
% 3.89/1.65  
% 3.89/1.65  
% 3.89/1.65  %Foreground operators:
% 3.89/1.65  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.89/1.65  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.89/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.89/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.89/1.65  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.89/1.65  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.89/1.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.89/1.65  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.89/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.89/1.65  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.89/1.65  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.89/1.65  tff('#skF_5', type, '#skF_5': $i).
% 3.89/1.65  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.89/1.65  tff('#skF_6', type, '#skF_6': $i).
% 3.89/1.65  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.89/1.65  tff('#skF_3', type, '#skF_3': $i).
% 3.89/1.65  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.89/1.65  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.89/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.89/1.65  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.89/1.65  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.89/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.89/1.65  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.89/1.65  tff('#skF_4', type, '#skF_4': $i).
% 3.89/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.89/1.65  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.89/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.89/1.65  
% 3.89/1.66  tff(f_86, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 3.89/1.66  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.89/1.66  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.89/1.66  tff(f_63, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.89/1.66  tff(f_75, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 3.89/1.66  tff(f_46, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.89/1.66  tff(f_44, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 3.89/1.66  tff(c_50, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.89/1.66  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.89/1.66  tff(c_90, plain, (![A_55, B_56]: (k4_xboole_0(A_55, B_56)=k1_xboole_0 | ~r1_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.89/1.66  tff(c_94, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_90])).
% 3.89/1.66  tff(c_44, plain, (![B_40]: (k4_xboole_0(k1_tarski(B_40), k1_tarski(B_40))!=k1_tarski(B_40))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.89/1.66  tff(c_95, plain, (![B_40]: (k1_tarski(B_40)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_94, c_44])).
% 3.89/1.66  tff(c_58, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.89/1.66  tff(c_56, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.89/1.66  tff(c_54, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.89/1.66  tff(c_52, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.89/1.66  tff(c_2347, plain, (![D_7253, C_7254, B_7255, A_7256]: (r2_hidden(k1_funct_1(D_7253, C_7254), B_7255) | k1_xboole_0=B_7255 | ~r2_hidden(C_7254, A_7256) | ~m1_subset_1(D_7253, k1_zfmisc_1(k2_zfmisc_1(A_7256, B_7255))) | ~v1_funct_2(D_7253, A_7256, B_7255) | ~v1_funct_1(D_7253))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.89/1.66  tff(c_2623, plain, (![D_7999, B_8000]: (r2_hidden(k1_funct_1(D_7999, '#skF_5'), B_8000) | k1_xboole_0=B_8000 | ~m1_subset_1(D_7999, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_8000))) | ~v1_funct_2(D_7999, '#skF_3', B_8000) | ~v1_funct_1(D_7999))), inference(resolution, [status(thm)], [c_52, c_2347])).
% 3.89/1.66  tff(c_2632, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_54, c_2623])).
% 3.89/1.66  tff(c_2635, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_2632])).
% 3.89/1.66  tff(c_2636, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_95, c_2635])).
% 3.89/1.66  tff(c_30, plain, (![A_11]: (k2_tarski(A_11, A_11)=k1_tarski(A_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.89/1.66  tff(c_119, plain, (![D_63, B_64, A_65]: (D_63=B_64 | D_63=A_65 | ~r2_hidden(D_63, k2_tarski(A_65, B_64)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.89/1.66  tff(c_125, plain, (![D_63, A_11]: (D_63=A_11 | D_63=A_11 | ~r2_hidden(D_63, k1_tarski(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_119])).
% 3.89/1.66  tff(c_2643, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_2636, c_125])).
% 3.89/1.66  tff(c_2693, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_50, c_2643])).
% 3.89/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.89/1.66  
% 3.89/1.66  Inference rules
% 3.89/1.66  ----------------------
% 3.89/1.66  #Ref     : 0
% 3.89/1.66  #Sup     : 320
% 3.89/1.66  #Fact    : 8
% 3.89/1.66  #Define  : 0
% 3.89/1.66  #Split   : 5
% 3.89/1.66  #Chain   : 0
% 3.89/1.66  #Close   : 0
% 3.89/1.66  
% 3.89/1.66  Ordering : KBO
% 3.89/1.66  
% 3.89/1.66  Simplification rules
% 3.89/1.66  ----------------------
% 3.89/1.66  #Subsume      : 56
% 3.89/1.66  #Demod        : 47
% 3.89/1.66  #Tautology    : 115
% 3.89/1.66  #SimpNegUnit  : 18
% 3.89/1.66  #BackRed      : 1
% 3.89/1.66  
% 3.89/1.66  #Partial instantiations: 3135
% 3.89/1.66  #Strategies tried      : 1
% 3.89/1.66  
% 3.89/1.66  Timing (in seconds)
% 3.89/1.66  ----------------------
% 3.89/1.66  Preprocessing        : 0.33
% 3.89/1.66  Parsing              : 0.18
% 3.89/1.66  CNF conversion       : 0.02
% 3.89/1.66  Main loop            : 0.56
% 3.89/1.66  Inferencing          : 0.32
% 3.89/1.66  Reduction            : 0.12
% 3.89/1.66  Demodulation         : 0.08
% 3.89/1.66  BG Simplification    : 0.03
% 3.89/1.66  Subsumption          : 0.08
% 3.89/1.66  Abstraction          : 0.03
% 3.89/1.66  MUC search           : 0.00
% 3.89/1.66  Cooper               : 0.00
% 3.89/1.66  Total                : 0.92
% 3.89/1.66  Index Insertion      : 0.00
% 3.89/1.66  Index Deletion       : 0.00
% 3.89/1.66  Index Matching       : 0.00
% 3.89/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
