%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:57 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   62 (  92 expanded)
%              Number of leaves         :   25 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :   80 ( 169 expanded)
%              Number of equality atoms :   13 (  24 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,A)
       => ( A != k1_xboole_0
         => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_44,plain,(
    m1_subset_1('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_86,plain,(
    ! [B_33,A_34] :
      ( v1_xboole_0(B_33)
      | ~ m1_subset_1(B_33,A_34)
      | ~ v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_90,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_86])).

tff(c_91,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_270,plain,(
    ! [A_63,B_64] :
      ( k4_xboole_0(k1_tarski(A_63),B_64) = k1_xboole_0
      | ~ r2_hidden(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | k4_xboole_0(A_6,B_7) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_34,plain,(
    ! [B_19,A_18] :
      ( r2_hidden(B_19,A_18)
      | ~ m1_subset_1(B_19,A_18)
      | v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_30,plain,(
    ! [A_16,B_17] :
      ( k4_xboole_0(k1_tarski(A_16),B_17) = k1_xboole_0
      | ~ r2_hidden(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_92,plain,(
    ! [B_35,A_36] :
      ( m1_subset_1(B_35,A_36)
      | ~ v1_xboole_0(B_35)
      | ~ v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_40,plain,(
    ~ m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_100,plain,
    ( ~ v1_xboole_0(k1_tarski('#skF_5'))
    | ~ v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_92,c_40])).

tff(c_102,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_18,plain,(
    ! [C_15,A_11] :
      ( r2_hidden(C_15,k1_zfmisc_1(A_11))
      | ~ r1_tarski(C_15,A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_119,plain,(
    ! [B_45,A_46] :
      ( m1_subset_1(B_45,A_46)
      | ~ r2_hidden(B_45,A_46)
      | v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_173,plain,(
    ! [C_54,A_55] :
      ( m1_subset_1(C_54,k1_zfmisc_1(A_55))
      | v1_xboole_0(k1_zfmisc_1(A_55))
      | ~ r1_tarski(C_54,A_55) ) ),
    inference(resolution,[status(thm)],[c_18,c_119])).

tff(c_179,plain,
    ( v1_xboole_0(k1_zfmisc_1('#skF_4'))
    | ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_173,c_40])).

tff(c_183,plain,(
    ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_179])).

tff(c_187,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_183])).

tff(c_191,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_187])).

tff(c_194,plain,
    ( ~ m1_subset_1('#skF_5','#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_191])).

tff(c_197,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_194])).

tff(c_199,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_197])).

tff(c_201,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_76,plain,(
    ! [C_29,A_30] :
      ( r2_hidden(C_29,k1_zfmisc_1(A_30))
      | ~ r1_tarski(C_29,A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_84,plain,(
    ! [A_30,C_29] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_30))
      | ~ r1_tarski(C_29,A_30) ) ),
    inference(resolution,[status(thm)],[c_76,c_2])).

tff(c_209,plain,(
    ! [C_56] : ~ r1_tarski(C_56,'#skF_4') ),
    inference(resolution,[status(thm)],[c_201,c_84])).

tff(c_214,plain,(
    ! [A_6] : k4_xboole_0(A_6,'#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_209])).

tff(c_284,plain,(
    ! [A_65] : ~ r2_hidden(A_65,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_214])).

tff(c_292,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_284])).

tff(c_299,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_292])).

tff(c_301,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_308,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_301,c_6])).

tff(c_312,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_308])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n023.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:02:36 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.29  
% 2.04/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.29  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 2.04/1.29  
% 2.04/1.29  %Foreground sorts:
% 2.04/1.29  
% 2.04/1.29  
% 2.04/1.29  %Background operators:
% 2.04/1.29  
% 2.04/1.29  
% 2.04/1.29  %Foreground operators:
% 2.04/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.04/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.04/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.04/1.29  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.04/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.04/1.29  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.04/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.04/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.04/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.04/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.04/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.04/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.04/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.29  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.04/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.04/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.04/1.29  
% 2.04/1.30  tff(f_75, negated_conjecture, ~(![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_subset_1)).
% 2.04/1.30  tff(f_67, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.04/1.30  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.04/1.30  tff(f_54, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 2.04/1.30  tff(f_39, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.04/1.30  tff(f_50, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.04/1.30  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.04/1.30  tff(c_42, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.04/1.30  tff(c_44, plain, (m1_subset_1('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.04/1.30  tff(c_86, plain, (![B_33, A_34]: (v1_xboole_0(B_33) | ~m1_subset_1(B_33, A_34) | ~v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.04/1.30  tff(c_90, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_44, c_86])).
% 2.04/1.30  tff(c_91, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_90])).
% 2.04/1.30  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.04/1.30  tff(c_270, plain, (![A_63, B_64]: (k4_xboole_0(k1_tarski(A_63), B_64)=k1_xboole_0 | ~r2_hidden(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.04/1.30  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | k4_xboole_0(A_6, B_7)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.04/1.30  tff(c_34, plain, (![B_19, A_18]: (r2_hidden(B_19, A_18) | ~m1_subset_1(B_19, A_18) | v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.04/1.30  tff(c_30, plain, (![A_16, B_17]: (k4_xboole_0(k1_tarski(A_16), B_17)=k1_xboole_0 | ~r2_hidden(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.04/1.30  tff(c_92, plain, (![B_35, A_36]: (m1_subset_1(B_35, A_36) | ~v1_xboole_0(B_35) | ~v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.04/1.30  tff(c_40, plain, (~m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.04/1.30  tff(c_100, plain, (~v1_xboole_0(k1_tarski('#skF_5')) | ~v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_92, c_40])).
% 2.04/1.30  tff(c_102, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_100])).
% 2.04/1.30  tff(c_18, plain, (![C_15, A_11]: (r2_hidden(C_15, k1_zfmisc_1(A_11)) | ~r1_tarski(C_15, A_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.04/1.30  tff(c_119, plain, (![B_45, A_46]: (m1_subset_1(B_45, A_46) | ~r2_hidden(B_45, A_46) | v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.04/1.30  tff(c_173, plain, (![C_54, A_55]: (m1_subset_1(C_54, k1_zfmisc_1(A_55)) | v1_xboole_0(k1_zfmisc_1(A_55)) | ~r1_tarski(C_54, A_55))), inference(resolution, [status(thm)], [c_18, c_119])).
% 2.04/1.30  tff(c_179, plain, (v1_xboole_0(k1_zfmisc_1('#skF_4')) | ~r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_173, c_40])).
% 2.04/1.30  tff(c_183, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_102, c_179])).
% 2.04/1.30  tff(c_187, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_183])).
% 2.04/1.30  tff(c_191, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_30, c_187])).
% 2.04/1.30  tff(c_194, plain, (~m1_subset_1('#skF_5', '#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_34, c_191])).
% 2.04/1.30  tff(c_197, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_194])).
% 2.04/1.30  tff(c_199, plain, $false, inference(negUnitSimplification, [status(thm)], [c_91, c_197])).
% 2.04/1.30  tff(c_201, plain, (v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_100])).
% 2.04/1.30  tff(c_76, plain, (![C_29, A_30]: (r2_hidden(C_29, k1_zfmisc_1(A_30)) | ~r1_tarski(C_29, A_30))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.04/1.30  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.04/1.30  tff(c_84, plain, (![A_30, C_29]: (~v1_xboole_0(k1_zfmisc_1(A_30)) | ~r1_tarski(C_29, A_30))), inference(resolution, [status(thm)], [c_76, c_2])).
% 2.04/1.30  tff(c_209, plain, (![C_56]: (~r1_tarski(C_56, '#skF_4'))), inference(resolution, [status(thm)], [c_201, c_84])).
% 2.04/1.30  tff(c_214, plain, (![A_6]: (k4_xboole_0(A_6, '#skF_4')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_209])).
% 2.04/1.30  tff(c_284, plain, (![A_65]: (~r2_hidden(A_65, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_270, c_214])).
% 2.04/1.30  tff(c_292, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_284])).
% 2.04/1.30  tff(c_299, plain, $false, inference(negUnitSimplification, [status(thm)], [c_91, c_292])).
% 2.04/1.30  tff(c_301, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_90])).
% 2.04/1.30  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.04/1.30  tff(c_308, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_301, c_6])).
% 2.04/1.30  tff(c_312, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_308])).
% 2.04/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.30  
% 2.04/1.30  Inference rules
% 2.04/1.30  ----------------------
% 2.04/1.30  #Ref     : 0
% 2.04/1.30  #Sup     : 53
% 2.04/1.30  #Fact    : 0
% 2.04/1.30  #Define  : 0
% 2.04/1.30  #Split   : 2
% 2.04/1.30  #Chain   : 0
% 2.04/1.30  #Close   : 0
% 2.04/1.30  
% 2.04/1.30  Ordering : KBO
% 2.04/1.30  
% 2.04/1.30  Simplification rules
% 2.04/1.30  ----------------------
% 2.04/1.30  #Subsume      : 4
% 2.04/1.30  #Demod        : 6
% 2.04/1.30  #Tautology    : 25
% 2.04/1.30  #SimpNegUnit  : 6
% 2.04/1.30  #BackRed      : 2
% 2.04/1.30  
% 2.04/1.30  #Partial instantiations: 0
% 2.04/1.30  #Strategies tried      : 1
% 2.04/1.30  
% 2.04/1.30  Timing (in seconds)
% 2.04/1.30  ----------------------
% 2.04/1.31  Preprocessing        : 0.30
% 2.04/1.31  Parsing              : 0.15
% 2.04/1.31  CNF conversion       : 0.02
% 2.04/1.31  Main loop            : 0.19
% 2.04/1.31  Inferencing          : 0.07
% 2.04/1.31  Reduction            : 0.05
% 2.04/1.31  Demodulation         : 0.03
% 2.04/1.31  BG Simplification    : 0.01
% 2.04/1.31  Subsumption          : 0.03
% 2.04/1.31  Abstraction          : 0.01
% 2.04/1.31  MUC search           : 0.00
% 2.04/1.31  Cooper               : 0.00
% 2.04/1.31  Total                : 0.52
% 2.04/1.31  Index Insertion      : 0.00
% 2.04/1.31  Index Deletion       : 0.00
% 2.04/1.31  Index Matching       : 0.00
% 2.04/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
