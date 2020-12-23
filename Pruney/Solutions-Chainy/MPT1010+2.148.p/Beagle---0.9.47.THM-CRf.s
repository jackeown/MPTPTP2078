%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:25 EST 2020

% Result     : Theorem 9.89s
% Output     : CNFRefutation 9.89s
% Verified   : 
% Statistics : Number of formulae       :   57 (  64 expanded)
%              Number of leaves         :   36 (  42 expanded)
%              Depth                    :    7
%              Number of atoms          :   65 (  96 expanded)
%              Number of equality atoms :   22 (  30 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_100,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_77,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_89,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_42,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_58,plain,(
    k1_funct_1('#skF_9','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_50,plain,(
    ! [A_42] :
      ( r2_hidden('#skF_5'(A_42),A_42)
      | k1_xboole_0 = A_42 ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_119,plain,(
    ! [D_68,A_69,B_70] :
      ( r2_hidden(D_68,A_69)
      | ~ r2_hidden(D_68,k4_xboole_0(A_69,B_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_124,plain,(
    ! [A_69,B_70] :
      ( r2_hidden('#skF_5'(k4_xboole_0(A_69,B_70)),A_69)
      | k4_xboole_0(A_69,B_70) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_50,c_119])).

tff(c_113,plain,(
    ! [D_65,B_66,A_67] :
      ( ~ r2_hidden(D_65,B_66)
      | ~ r2_hidden(D_65,k4_xboole_0(A_67,B_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_881,plain,(
    ! [A_1796,B_1797] :
      ( ~ r2_hidden('#skF_5'(k4_xboole_0(A_1796,B_1797)),B_1797)
      | k4_xboole_0(A_1796,B_1797) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_50,c_113])).

tff(c_891,plain,(
    ! [A_69] : k4_xboole_0(A_69,A_69) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_124,c_881])).

tff(c_46,plain,(
    ! [B_41] : k4_xboole_0(k1_tarski(B_41),k1_tarski(B_41)) != k1_tarski(B_41) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_892,plain,(
    ! [B_41] : k1_tarski(B_41) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_891,c_46])).

tff(c_66,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_64,plain,(
    v1_funct_2('#skF_9','#skF_6',k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_62,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6',k1_tarski('#skF_7')))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_60,plain,(
    r2_hidden('#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_17126,plain,(
    ! [D_84849,C_84850,B_84851,A_84852] :
      ( r2_hidden(k1_funct_1(D_84849,C_84850),B_84851)
      | k1_xboole_0 = B_84851
      | ~ r2_hidden(C_84850,A_84852)
      | ~ m1_subset_1(D_84849,k1_zfmisc_1(k2_zfmisc_1(A_84852,B_84851)))
      | ~ v1_funct_2(D_84849,A_84852,B_84851)
      | ~ v1_funct_1(D_84849) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_17268,plain,(
    ! [D_86424,B_86425] :
      ( r2_hidden(k1_funct_1(D_86424,'#skF_8'),B_86425)
      | k1_xboole_0 = B_86425
      | ~ m1_subset_1(D_86424,k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_86425)))
      | ~ v1_funct_2(D_86424,'#skF_6',B_86425)
      | ~ v1_funct_1(D_86424) ) ),
    inference(resolution,[status(thm)],[c_60,c_17126])).

tff(c_17331,plain,
    ( r2_hidden(k1_funct_1('#skF_9','#skF_8'),k1_tarski('#skF_7'))
    | k1_tarski('#skF_7') = k1_xboole_0
    | ~ v1_funct_2('#skF_9','#skF_6',k1_tarski('#skF_7'))
    | ~ v1_funct_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_62,c_17268])).

tff(c_17334,plain,
    ( r2_hidden(k1_funct_1('#skF_9','#skF_8'),k1_tarski('#skF_7'))
    | k1_tarski('#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_17331])).

tff(c_17335,plain,(
    r2_hidden(k1_funct_1('#skF_9','#skF_8'),k1_tarski('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_892,c_17334])).

tff(c_20,plain,(
    ! [C_11,A_7] :
      ( C_11 = A_7
      | ~ r2_hidden(C_11,k1_tarski(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_17350,plain,(
    k1_funct_1('#skF_9','#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_17335,c_20])).

tff(c_17473,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_17350])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:51:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.89/3.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.89/3.21  
% 9.89/3.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.89/3.22  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_4
% 9.89/3.22  
% 9.89/3.22  %Foreground sorts:
% 9.89/3.22  
% 9.89/3.22  
% 9.89/3.22  %Background operators:
% 9.89/3.22  
% 9.89/3.22  
% 9.89/3.22  %Foreground operators:
% 9.89/3.22  tff('#skF_5', type, '#skF_5': $i > $i).
% 9.89/3.22  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 9.89/3.22  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.89/3.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.89/3.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.89/3.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.89/3.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.89/3.22  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 9.89/3.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.89/3.22  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 9.89/3.22  tff('#skF_7', type, '#skF_7': $i).
% 9.89/3.22  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 9.89/3.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.89/3.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.89/3.22  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.89/3.22  tff('#skF_6', type, '#skF_6': $i).
% 9.89/3.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.89/3.22  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 9.89/3.22  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.89/3.22  tff('#skF_9', type, '#skF_9': $i).
% 9.89/3.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.89/3.22  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 9.89/3.22  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 9.89/3.22  tff('#skF_8', type, '#skF_8': $i).
% 9.89/3.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.89/3.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.89/3.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.89/3.22  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 9.89/3.22  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 9.89/3.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.89/3.22  
% 9.89/3.23  tff(f_100, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 9.89/3.23  tff(f_77, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 9.89/3.23  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 9.89/3.23  tff(f_61, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 9.89/3.23  tff(f_89, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 9.89/3.23  tff(f_42, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 9.89/3.23  tff(c_58, plain, (k1_funct_1('#skF_9', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.89/3.23  tff(c_50, plain, (![A_42]: (r2_hidden('#skF_5'(A_42), A_42) | k1_xboole_0=A_42)), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.89/3.23  tff(c_119, plain, (![D_68, A_69, B_70]: (r2_hidden(D_68, A_69) | ~r2_hidden(D_68, k4_xboole_0(A_69, B_70)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.89/3.23  tff(c_124, plain, (![A_69, B_70]: (r2_hidden('#skF_5'(k4_xboole_0(A_69, B_70)), A_69) | k4_xboole_0(A_69, B_70)=k1_xboole_0)), inference(resolution, [status(thm)], [c_50, c_119])).
% 9.89/3.23  tff(c_113, plain, (![D_65, B_66, A_67]: (~r2_hidden(D_65, B_66) | ~r2_hidden(D_65, k4_xboole_0(A_67, B_66)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.89/3.23  tff(c_881, plain, (![A_1796, B_1797]: (~r2_hidden('#skF_5'(k4_xboole_0(A_1796, B_1797)), B_1797) | k4_xboole_0(A_1796, B_1797)=k1_xboole_0)), inference(resolution, [status(thm)], [c_50, c_113])).
% 9.89/3.23  tff(c_891, plain, (![A_69]: (k4_xboole_0(A_69, A_69)=k1_xboole_0)), inference(resolution, [status(thm)], [c_124, c_881])).
% 9.89/3.23  tff(c_46, plain, (![B_41]: (k4_xboole_0(k1_tarski(B_41), k1_tarski(B_41))!=k1_tarski(B_41))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.89/3.23  tff(c_892, plain, (![B_41]: (k1_tarski(B_41)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_891, c_46])).
% 9.89/3.23  tff(c_66, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.89/3.23  tff(c_64, plain, (v1_funct_2('#skF_9', '#skF_6', k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.89/3.23  tff(c_62, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', k1_tarski('#skF_7'))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.89/3.23  tff(c_60, plain, (r2_hidden('#skF_8', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.89/3.23  tff(c_17126, plain, (![D_84849, C_84850, B_84851, A_84852]: (r2_hidden(k1_funct_1(D_84849, C_84850), B_84851) | k1_xboole_0=B_84851 | ~r2_hidden(C_84850, A_84852) | ~m1_subset_1(D_84849, k1_zfmisc_1(k2_zfmisc_1(A_84852, B_84851))) | ~v1_funct_2(D_84849, A_84852, B_84851) | ~v1_funct_1(D_84849))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.89/3.23  tff(c_17268, plain, (![D_86424, B_86425]: (r2_hidden(k1_funct_1(D_86424, '#skF_8'), B_86425) | k1_xboole_0=B_86425 | ~m1_subset_1(D_86424, k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_86425))) | ~v1_funct_2(D_86424, '#skF_6', B_86425) | ~v1_funct_1(D_86424))), inference(resolution, [status(thm)], [c_60, c_17126])).
% 9.89/3.23  tff(c_17331, plain, (r2_hidden(k1_funct_1('#skF_9', '#skF_8'), k1_tarski('#skF_7')) | k1_tarski('#skF_7')=k1_xboole_0 | ~v1_funct_2('#skF_9', '#skF_6', k1_tarski('#skF_7')) | ~v1_funct_1('#skF_9')), inference(resolution, [status(thm)], [c_62, c_17268])).
% 9.89/3.23  tff(c_17334, plain, (r2_hidden(k1_funct_1('#skF_9', '#skF_8'), k1_tarski('#skF_7')) | k1_tarski('#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_17331])).
% 9.89/3.23  tff(c_17335, plain, (r2_hidden(k1_funct_1('#skF_9', '#skF_8'), k1_tarski('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_892, c_17334])).
% 9.89/3.23  tff(c_20, plain, (![C_11, A_7]: (C_11=A_7 | ~r2_hidden(C_11, k1_tarski(A_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.89/3.23  tff(c_17350, plain, (k1_funct_1('#skF_9', '#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_17335, c_20])).
% 9.89/3.23  tff(c_17473, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_17350])).
% 9.89/3.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.89/3.23  
% 9.89/3.23  Inference rules
% 9.89/3.23  ----------------------
% 9.89/3.23  #Ref     : 0
% 9.89/3.23  #Sup     : 2656
% 9.89/3.23  #Fact    : 2
% 9.89/3.23  #Define  : 0
% 9.89/3.23  #Split   : 11
% 9.89/3.23  #Chain   : 0
% 9.89/3.23  #Close   : 0
% 9.89/3.23  
% 9.89/3.23  Ordering : KBO
% 9.89/3.23  
% 9.89/3.23  Simplification rules
% 9.89/3.23  ----------------------
% 9.89/3.23  #Subsume      : 502
% 9.89/3.23  #Demod        : 612
% 9.89/3.23  #Tautology    : 280
% 9.89/3.23  #SimpNegUnit  : 140
% 9.89/3.23  #BackRed      : 35
% 9.89/3.23  
% 9.89/3.23  #Partial instantiations: 30119
% 9.89/3.23  #Strategies tried      : 1
% 9.89/3.23  
% 9.89/3.23  Timing (in seconds)
% 9.89/3.23  ----------------------
% 9.89/3.23  Preprocessing        : 0.36
% 9.89/3.23  Parsing              : 0.19
% 9.89/3.23  CNF conversion       : 0.03
% 9.89/3.23  Main loop            : 2.05
% 9.89/3.23  Inferencing          : 1.05
% 9.89/3.23  Reduction            : 0.46
% 9.89/3.23  Demodulation         : 0.30
% 9.89/3.23  BG Simplification    : 0.09
% 9.89/3.23  Subsumption          : 0.35
% 9.89/3.23  Abstraction          : 0.12
% 9.89/3.23  MUC search           : 0.00
% 9.89/3.23  Cooper               : 0.00
% 9.89/3.23  Total                : 2.44
% 9.89/3.23  Index Insertion      : 0.00
% 9.89/3.23  Index Deletion       : 0.00
% 9.89/3.23  Index Matching       : 0.00
% 9.89/3.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
